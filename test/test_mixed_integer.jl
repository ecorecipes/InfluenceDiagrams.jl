# `MixedIntegerPolicySearch` (the JuMP extension) and the rooted junction tree it is stated
# on, checked against the other backends.
using JuMP: JuMP
using HiGHS: HiGHS

# A herd followed for `stages` periods: its health is hidden, a test is read each period,
# and the decision to treat sees only that period's test. A limited-memory diagram whose
# joint states grow as `8^stages` while its clusters stay small.
function herd_model(rng::AbstractRNG, stages::Int)
    health = [Symbol(:H, t) for t in 1:(stages + 1)]
    tests = [Symbol(:T, t) for t in 1:stages]
    treat = [Symbol(:D, t) for t in 1:stages]
    id = influence_diagram((h => [:ill, :healthy] for h in health)...,
                           (x => [:positive, :negative] for x in tests)...,
                           (d => [:treat, :leave] for d in treat)...;
                           mechanisms=vcat([tests[t] => health[t] for t in 1:stages],
                                           [health[t + 1] => (health[t], treat[t])
                                            for t in 1:stages]),
                           decisions=[treat[t] => tests[t] for t in 1:stages],
                           utilities=vcat([Symbol(:C, t) => treat[t] for t in 1:stages],
                                          [:Sale => health[end]]))
    m = bind_cpt(InfluenceDiagramModel(id), health[1] => [0.1, 0.9])
    for t in 1:stages
        m = bind_cpt(m, tests[t] => [0.8 0.2; 0.1 0.9])
        # (health, treat) -> next health
        next = zeros(2, 2, 2)
        next[1, 1, :] = [0.5, 0.5]
        next[1, 2, :] = [0.9, 0.1]
        next[2, 1, :] = [0.1, 0.9]
        next[2, 2, :] = [0.2, 0.8]
        m = bind_cpt(m, health[t + 1] => next)
        m = bind_utility(m, Symbol(:C, t) => [-100.0 - 10 * rand(rng), 0.0])
    end
    return bind_utility(m, :Sale => [300.0, 1000.0])
end

@testset "MixedIntegerPolicySearch" begin
    @test Base.get_extension(InfluenceDiagrams, :InfluenceDiagramsJuMPExt) !== nothing
    mip = MixedIntegerPolicySearch(HiGHS.Optimizer)

    @testset "construction" begin
        @test mip isa DecisionBackend
        @test mip.silent && mip.max_cluster_states == 1_000_000
        @test !MixedIntegerPolicySearch(HiGHS.Optimizer; silent=false).silent
        @test_throws ArgumentError MixedIntegerPolicySearch(HiGHS.Optimizer;
                                                            max_cluster_states=0)
    end

    @testset "the rooted junction tree" begin
        tree = rooted_junction_tree(umbrella_model())
        @test tree.order == [:Weather, :Forecast, :Umbrella]
        @test tree.clusters[:Umbrella] == [:Weather, :Forecast, :Umbrella]
        @test tree.clusters[:Forecast] == [:Weather, :Forecast]
        @test tree.parent ==
              Dict(:Weather => nothing, :Forecast => :Weather, :Umbrella => :Forecast)
        @test_throws UnknownVariableError rooted_junction_tree(syntax(umbrella_model());
                                                               scopes=[[:Nowhere]])
        rng = MersenneTwister(4)
        for trial in 1:60
            m = random_influence_model(rng; max_actions=3, max_chance_states=3)
            iseven(trial) && (m = forgetful(rng, m))
            id = syntax(m)
            tree = rooted_junction_tree(id)
            position = Dict(x => i for (i, x) in enumerate(tree.order))
            @test sort(tree.order) == sort(variable_names(id))
            parents = InfluenceDiagrams._decision_parents(id)
            for x in tree.order
                cluster = tree.clusters[x]
                # Its own variable last, its family inside, in topological order.
                @test last(cluster) == x && issorted(cluster; by=y -> position[y])
                @test issubset(parents[x], cluster)
                @test all(position[p] < position[x] for p in parents[x])
                # What it passes up is in its parent's cluster.
                up = tree.parent[x]
                if up === nothing
                    @test cluster == [x]
                else
                    @test issubset(cluster[1:(end - 1)], tree.clusters[up])
                    @test up == cluster[end - 1]
                end
            end
            # Some cluster holds each utility's scope.
            for u in InfluenceDiagrams.utilities(id)
                scope = utility_scope_names(id, u)
                @test isempty(scope) ||
                      any(issubset(scope, tree.clusters[x]) for x in tree.order)
            end
            # Running intersection: the clusters holding a variable are connected.
            for y in tree.order
                holders = [x for x in tree.order if y in tree.clusters[x]]
                @test count(x -> tree.parent[x] === nothing ||
                                !(y in tree.clusters[tree.parent[x]]), holders) == 1
            end
        end
    end

    @testset "the examples" begin
        for m in (umbrella_model(), two_stage_model(), reference_grazing_model())
            solution = optimize(m, mip)
            @test solution.expected_utility ≈ optimize(m).expected_utility
            @test expected_utility(m, solution.strategy) ≈ solution.expected_utility
            d = solution.diagnostics
            @test d.method === :mixed_integer && d.verified && d.status === :OPTIMAL
            @test d.objective ≈ solution.expected_utility
            @test d.nstrategies == n_deterministic_strategies(m)
            @test d.clusters == length(variable_names(syntax(m)))
        end
    end

    @testset "random diagrams, with and without no-forgetting" begin
        rng = MersenneTwister(7)
        limited = 0
        for trial in 1:80
            m = random_influence_model(rng; max_actions=3, max_chance_states=4,
                                       max_info_states=4)
            iseven(trial) && (m = forgetful(rng, m))
            is_no_forgetting(m) || (limited += 1)
            reference = optimize(m, BranchAndBoundPolicySearch())
            solution = optimize(m, mip)
            @test isapprox(solution.expected_utility, reference.expected_utility;
                           atol=1e-6)
            @test isapprox(solution.diagnostics.objective, reference.expected_utility;
                           atol=1e-6)
        end
        @test limited >= 8
    end

    @testset "team problems" begin
        rng = MersenneTwister(3)
        for (nsignals, nactions, ndecisions) in ((3, 3, 2), (4, 3, 2), (3, 2, 3)), _ in 1:5
            m = team_model(rng, nsignals, nactions; ndecisions)
            @test isapprox(optimize(m, mip).expected_utility,
                           optimize(m, ExhaustivePolicySearch()).expected_utility;
                           atol=1e-6)
        end
    end

    @testset "a diagram too large to enumerate at the default limits" begin
        m = herd_model(MersenneTwister(9), 7)
        @test !is_no_forgetting(m)
        joint = prod(big(length(states(syntax(m), x))) for x in variable_names(syntax(m)))
        @test joint == big(2)^22
        solution = optimize(m, mip)
        d = solution.diagnostics
        # Past `max_states` the value is the solver's objective, and says so.
        @test !d.verified && solution.expected_utility == d.objective
        @test d.largest_cluster <= 16
        # The other backends refuse at their defaults and agree when allowed the states.
        @test_throws ModelTooLargeError optimize(m, BranchAndBoundPolicySearch())
        search = optimize(m, BranchAndBoundPolicySearch(); max_states=5_000_000)
        @test isapprox(solution.expected_utility, search.expected_utility; rtol=1e-8)
        @test isapprox(expected_utility(m, solution.strategy; max_states=5_000_000),
                       search.expected_utility; rtol=1e-8)
        verified = optimize(m, mip; max_states=5_000_000)
        @test verified.diagnostics.verified
        @test isapprox(verified.expected_utility, search.expected_utility; rtol=1e-8)
    end

    @testset "what it refuses" begin
        m = umbrella_model()
        @test_throws ArgumentError optimize(observe(m, :Forecast => :rainy), mip)
        @test_throws ArgumentError optimize(m, mip;
                                            context=DecisionContext(;
                                                                    terminal=([:Weather],
                                                                              [1.0, 2.0])))
        @test optimize(m, mip; context=DecisionContext()).expected_utility ≈ 77
        @test_throws ModelTooLargeError optimize(m,
                                                 MixedIntegerPolicySearch(HiGHS.Optimizer;
                                                                          max_cluster_states=4))
        @test_throws UtilityScopeError optimize(bind_utility(m, :U => [NaN 1.0; 2.0 3.0]),
                                                mip)
        @test_throws IrregularDiagramError optimize(team_model(MersenneTwister(1), 3, 2))
        @test occursin("TIME_LIMIT",
                       sprint(showerror, MixedIntegerSolverError(:TIME_LIMIT)))
    end
end
