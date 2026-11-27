# `BranchAndBoundPolicySearch`: checked against the exhaustive oracle wherever the oracle
# can run, and against separately solved subproblems where it cannot.

# Two or more decisions that each see a private signal of one hidden state and share one
# utility: a limited-memory diagram whose relaxation is not tight, so the search branches.
function team_model(rng::AbstractRNG, nsignals::Int, nactions::Int; ndecisions::Int=2)
    labels(prefix, n) = [Symbol(prefix, i) for i in 1:n]
    signals = [Symbol(:X, i) for i in 1:ndecisions]
    choices = [Symbol(:D, i) for i in 1:ndecisions]
    id = influence_diagram(:W => labels("w", 2),
                           (x => labels(lowercase(string(x)), nsignals) for x in signals)...,
                           (d => labels(lowercase(string(d)), nactions) for d in choices)...;
                           mechanisms=[x => :W for x in signals],
                           decisions=[d => x for (d, x) in zip(choices, signals)],
                           utilities=[:U => (:W, choices...)])
    m = bind_cpt(InfluenceDiagramModel(id), :W => [0.4, 0.6])
    for x in signals
        t = rand(rng, 2, nsignals) .+ 0.05
        m = bind_cpt(m, x => t ./ sum(t; dims=2))
    end
    return bind_utility(m, :U => 10 .* rand(rng, 2, ntuple(_ -> nactions, ndecisions)...))
end

# Drop each information arc with probability one half.
function forgetful(rng::AbstractRNG, m::InfluenceDiagramModel)
    id = syntax(m)
    for d in decision_names(id), x in information_names(id, d)
        rand(rng) < 0.5 && (m = without_information(m, d, x))
    end
    return m
end

@testset "BranchAndBoundPolicySearch" begin
    @testset "construction" begin
        @test BranchAndBoundPolicySearch() isa DecisionBackend
        @test BranchAndBoundPolicySearch().max_nodes == 1_000_000
        @test BranchAndBoundPolicySearch(; max_nodes=7).max_nodes == 7
        @test_throws ArgumentError BranchAndBoundPolicySearch(; max_nodes=0)
    end

    @testset "the examples" begin
        for m in (umbrella_model(), two_stage_model(), reference_grazing_model())
            dve = optimize(m)
            bb = optimize(m, BranchAndBoundPolicySearch())
            @test bb.expected_utility ≈ dve.expected_utility
            @test expected_utility(m, bb.strategy) ≈ bb.expected_utility
            @test bb.diagnostics.method === :branch_and_bound
            @test bb.diagnostics.nstrategies == n_deterministic_strategies(m)
            @test bb.diagnostics.nodes >= 1 && bb.diagnostics.ratio_iterations >= 1
            # The bound is above the optimum and the starting incumbent below it.
            @test bb.diagnostics.root_bound >= bb.expected_utility - 1e-9
            @test bb.diagnostics.incumbent_start <= bb.expected_utility + 1e-9
        end
        @test optimize(umbrella_model();
                       backend=BranchAndBoundPolicySearch()).expected_utility ≈
              77
    end

    @testset "random diagrams, with and without no-forgetting, against the oracle" begin
        rng = MersenneTwister(7)
        compared = 0
        limited = 0
        for trial in 1:200
            m = random_influence_model(rng; max_actions=3, max_chance_states=4,
                                       max_info_states=4)
            iseven(trial) && (m = forgetful(rng, m))
            ex = try
                optimize(m, ExhaustivePolicySearch())
            catch e
                e isa PolicySearchTooLargeError || rethrow()
                continue
            end
            bb = optimize(m, BranchAndBoundPolicySearch())
            compared += 1
            is_no_forgetting(m) || (limited += 1)
            @test isapprox(bb.expected_utility, ex.expected_utility; atol=1e-9)
            @test isapprox(expected_utility(m, bb.strategy), ex.expected_utility;
                           atol=1e-9)
            is_no_forgetting(m) &&
                @test isapprox(bb.expected_utility, optimize(m).expected_utility;
                               atol=1e-9)
        end
        @test compared >= 150
        @test limited >= 20
    end

    @testset "team problems: the search has to branch" begin
        rng = MersenneTwister(3)
        branched = 0
        improved = 0
        for (nsignals, nactions, ndecisions) in ((3, 3, 2), (4, 3, 2), (3, 2, 3)), _ in 1:10
            m = team_model(rng, nsignals, nactions; ndecisions)
            @test !is_no_forgetting(m)
            @test_throws IrregularDiagramError optimize(m)
            ex = optimize(m, ExhaustivePolicySearch())
            bb = optimize(m, BranchAndBoundPolicySearch())
            @test isapprox(bb.expected_utility, ex.expected_utility; atol=1e-9)
            @test isapprox(expected_utility(m, bb.strategy), ex.expected_utility;
                           atol=1e-9)
            bb.diagnostics.nodes > 1 && (branched += 1)
            bb.diagnostics.incumbent_start < bb.expected_utility - 1e-9 && (improved += 1)
        end
        # The relaxation is not always tight here, and single policy updating does not
        # always reach the optimum: both parts of the search are exercised.
        @test branched >= 10
        @test improved >= 3
    end

    @testset "beyond the oracle" begin
        # 4^10 * 4^10 strategies. The value is bracketed by the search's own bound and
        # by a strategy the reference evaluator scores.
        m = team_model(MersenneTwister(11), 10, 4)
        @test n_deterministic_strategies(m) == big(4)^20
        @test_throws PolicySearchTooLargeError optimize(m, ExhaustivePolicySearch())
        bb = optimize(m, BranchAndBoundPolicySearch())
        @test expected_utility(m, bb.strategy) ≈ bb.expected_utility
        @test bb.diagnostics.incumbent_start <= bb.expected_utility + 1e-9
        @test bb.expected_utility <= bb.diagnostics.root_bound + 1e-9
        # With perfect recall the value can only rise (and DVE solves that diagram).
        @test bb.expected_utility <=
              optimize(with_no_forgetting(m)).expected_utility + 1e-9

        # Two decisions that share nothing: the optimum is the sum of the two parts,
        # each solved alone by decision variable elimination.
        labels(prefix, n) = [Symbol(prefix, i) for i in 1:n]
        rng = MersenneTwister(5)
        probabilities() = (p = rand(rng, 6) .+ 0.1; p ./ sum(p))
        px, py = probabilities(), probabilities()
        u, v = 10 .* rand(rng, 6, 4), 10 .* rand(rng, 6, 4)
        function part(x, d, name, p, table)
            id = influence_diagram(x => labels("s", 6), d => labels("a", 4);
                                   decisions=[d => x], utilities=[name => (x, d)])
            return bind_utility(bind_cpt(InfluenceDiagramModel(id), x => p), name => table)
        end
        id = influence_diagram(:X => labels("s", 6), :Y => labels("s", 6),
                               :D => labels("a", 4), :E => labels("a", 4);
                               decisions=[:D => :X, :E => :Y],
                               utilities=[:U => (:X, :D), :V => (:Y, :E)])
        both = bind_cpt(InfluenceDiagramModel(id), [:X => px, :Y => py])
        both = bind_utility(both, [:U => u, :V => v])
        @test !is_no_forgetting(both)
        separate = optimize(part(:X, :D, :U, px, u)).expected_utility +
                   optimize(part(:Y, :E, :V, py, v)).expected_utility
        @test optimize(both, BranchAndBoundPolicySearch()).expected_utility ≈ separate
    end

    @testset "forgetting changes the optimum, as the oracle finds it" begin
        diagram = influence_diagram(:Weather => [:zero, :one],
                                    :SignalAction => [:quiet, :signal],
                                    :Guess => [:zero, :one];
                                    decisions=[:SignalAction => :Weather,
                                               :Guess => :SignalAction],
                                    utilities=[:Cost => :SignalAction,
                                               :Reward => (:Weather, :Guess)])
        model = bind_cpt(InfluenceDiagramModel(diagram), :Weather => [0.25, 0.75])
        model = bind_utility(model, [:Cost => [0.0, -2.0], :Reward => [1.0 0.0; 0.0 1.0]])
        @test optimize(model, BranchAndBoundPolicySearch()).expected_utility ≈ 0.75
        @test optimize(with_no_forgetting(model),
                       BranchAndBoundPolicySearch()).expected_utility ≈
              1.0
    end

    @testset "kernels accepted within the tolerance are not renormalised" begin
        # The mass then depends on the strategy, and the ratio the oracle maximises is
        # what the search maximises too.
        rng = MersenneTwister(21)
        for _ in 1:20
            m = team_model(rng, 3, 2)
            table = rand(rng, 2, 3) .+ 0.05
            table ./= sum(table; dims=2)
            table[1, 1] += 5e-7
            loose = bind_cpt(m, :X1 => table; atol=1e-5)
            ex = optimize(loose, ExhaustivePolicySearch(); atol=1e-5)
            bb = optimize(loose, BranchAndBoundPolicySearch(); atol=1e-5)
            @test isapprox(bb.expected_utility, ex.expected_utility; atol=1e-12)
        end
    end

    @testset "what it refuses" begin
        m = umbrella_model()
        @test_throws ArgumentError optimize(observe(m, :Forecast => :rainy),
                                            BranchAndBoundPolicySearch())
        @test_throws ArgumentError optimize(m, BranchAndBoundPolicySearch();
                                            context=DecisionContext(;
                                                                    terminal=([:Weather],
                                                                              [1.0, 2.0])))
        # An empty context is no context.
        @test optimize(m, BranchAndBoundPolicySearch();
                       context=DecisionContext()).expected_utility ≈
              77
        @test_throws ModelTooLargeError optimize(m, BranchAndBoundPolicySearch();
                                                 max_states=2)
        hard = team_model(MersenneTwister(3), 4, 3)
        @test optimize(hard, BranchAndBoundPolicySearch()).diagnostics.nodes > 3
        err = try
            optimize(hard, BranchAndBoundPolicySearch(; max_nodes=3))
        catch e
            e
        end
        @test err isa SearchNodeLimitError
        @test err.limit == 3 && err.nodes > 3
        @test occursin("max_nodes", sprint(showerror, err))
        # A NaN utility has no expected value, for this backend as for the others.
        @test_throws UtilityScopeError optimize(bind_utility(m,
                                                             :U => [NaN 1.0;
                                                                    2.0 3.0]),
                                                BranchAndBoundPolicySearch())
    end
end
