# ADR 0014: `ImpossibleEvidenceError` means probability exactly zero. A binary64 evidence
# mass that underflows is recomputed exactly, and a mass that tolerated negative entries
# leave undetermined is `IndeterminatePosteriorError`.
@testset "Evidence mass" begin
    function rare_model(pa)
        id = influence_diagram(:A => [:rare, :usual], :B => [:rare, :usual],
                               :D => [:leave, :act];
                               decisions=[:D => ()], utilities=[:Value => :D])
        m = bind_cpt(InfluenceDiagramModel(id), [:A => pa, :B => [1e-200, 1.0]])
        return observe(bind_utility(m, :Value => [-2.0, 3.0]), [:A => :rare, :B => :rare])
    end

    @testset "underflowed evidence falls back to exact arithmetic" begin
        rare = rare_model([1e-200, 1.0])
        dve = optimize(rare)
        @test dve.expected_utility == 3.0
        @test all(==(:act), policy_table(dve.strategy[:D]))
        @test dve.diagnostics.exact_fallback
        @test dve.diagnostics.arithmetic == :exact_rational
        exhaustive = optimize(rare, ExhaustivePolicySearch())
        @test exhaustive.expected_utility == 3.0
        @test exhaustive.diagnostics.exact_fallback
        @test expected_utility(rare, dve.strategy) == 3.0

        # A normal mass takes the binary64 path and records no fallback.
        ordinary = rare_model([0.5, 0.5])
        @test !haskey(optimize(ordinary).diagnostics, :exact_fallback)
        @test !haskey(optimize(ordinary, ExhaustivePolicySearch()).diagnostics,
                      :exact_fallback)
    end

    @testset "an exact zero is still impossible" begin
        impossible = rare_model([0.0, 1.0])
        @test_throws ImpossibleEvidenceError optimize(impossible)
        @test_throws ImpossibleEvidenceError optimize(impossible, ExhaustivePolicySearch())
        @test_throws ImpossibleEvidenceError optimize(impossible,
                                                      ExhaustivePolicySearch(;
                                                                             brute_force=true))
    end

    @testset "tolerated negative entries" begin
        id = influence_diagram(:X => [:a, :b], :Y => [:a, :b], :D => [:leave, :act];
                               mechanisms=[:X => (), :Y => (:X,)],
                               decisions=[:D => ()], utilities=[:U => (:Y, :D)])
        base = InfluenceDiagramModel(id)
        util = :U => [0.0 1.0; 2.0 3.0]

        # The evidence mass is itself negative.
        negative = bind_utility(bind_cpt(base,
                                         [:X => [1 + 1e-7, -1e-7],
                                          :Y => [0.5 0.5; 0.5 0.5]]; atol=1e-6),
                                util)
        negative = observe(negative, :X => :b)
        @test_throws BayesianNetworks.IndeterminatePosteriorError optimize(negative;
                                                                           atol=1e-6)
        @test_throws BayesianNetworks.IndeterminatePosteriorError optimize(negative,
                                                                           ExhaustivePolicySearch();
                                                                           atol=1e-6)

        # A positive, normal mass that is within the tolerance budget of zero, with the
        # negative entry on the evidence (X = b, Y = b).
        budget = bind_utility(bind_cpt(base,
                                       [:X => [1 - 1e-6, 1e-6],
                                        :Y => [0.5 0.5; 1+1e-7 -1e-7]]; atol=1e-6),
                              util)
        budget = observe(budget, :X => :b)
        for backend in (DecisionVariableElimination(), ExhaustivePolicySearch(),
                        ExhaustivePolicySearch(; brute_force=true))
            @test_throws BayesianNetworks.IndeterminatePosteriorError optimize(budget,
                                                                               backend;
                                                                               atol=1e-6)
        end
        # The same mass with the negative entry on X = a, which the evidence rules out: the
        # entry takes no part in the posterior, so the answer is determined (BayesianNetworks'
        # rule for `marginal`, which the exhaustive search applies to each strategy).
        ruled_out = bind_utility(bind_cpt(base,
                                          [:X => [1 - 1e-6, 1e-6],
                                           :Y => [1+1e-7 -1e-7; 0.5 0.5]]; atol=1e-6),
                                 util)
        ruled_out = observe(ruled_out, :X => :b)
        @test optimize(ruled_out; atol=1e-6).expected_utility == 2.0
        @test optimize(ruled_out, ExhaustivePolicySearch(); atol=1e-6).expected_utility ==
              2.0
        @test optimize(ruled_out, ExhaustivePolicySearch(; brute_force=true);
                       atol=1e-6).expected_utility == 2.0

        # Review finding 4: two negative entries on one joint state (X = b, Y = b) give a
        # positive product, so no value-table product is unreliable and the value-table
        # search, which had no budget check, returned a value. Both entries take part, and
        # the evidence mass, about 1e-6, is within the budget.
        paired = bind_utility(bind_cpt(base,
                                       [:X => [1 + 1e-7, -1e-7],
                                        :Y => [1-1e-6 1e-6; 1+1e-7 -1e-7]]; atol=1e-6),
                              util)
        paired = observe(paired, :Y => :b)
        for backend in (DecisionVariableElimination(), ExhaustivePolicySearch(),
                        ExhaustivePolicySearch(; brute_force=true))
            e = try
                optimize(paired, backend; atol=1e-6)
            catch err
                err
            end
            @test e isa BayesianNetworks.IndeterminatePosteriorError &&
                  occursin("budget", e.detail)
        end

        # Away from the budget the negative entry is harmless.
        clear = bind_utility(bind_cpt(base,
                                      [:X => [0.5, 0.5],
                                       :Y => [1+1e-7 -1e-7; 0.5 0.5]]; atol=1e-6),
                             util)
        @test optimize(observe(clear, :X => :b); atol=1e-6).expected_utility ≈ 2.0
        # Exact arithmetic does not accept a tolerated negative entry (ADR 0015).
        domain = try
            optimize(clear, DecisionVariableElimination(; stable=true); atol=1e-6)
        catch e
            e
        end
        @test domain isa FactorDomainError
        @test domain.backend === :stable_decision_elimination && domain.value == -1e-7
    end

    # Review finding 1: the binary64 DVE run took its budget from the constancy tolerance
    # and had no negative-posterior-cell check, so it returned values the other backends
    # refuse. Every backend now raises in the same cases, with the same condition.
    @testset "tolerated negative entries: DVE raises where the other backends do" begin
        id = influence_diagram(:X => [:a, :b], :Y => [:a, :b], :D => [:leave, :act];
                               mechanisms=[:X => (), :Y => (:X,)],
                               decisions=[:D => ()], utilities=[:U => (:X, :D)])
        function model(px, py, observed)
            m = bind_cpt(InfluenceDiagramModel(id), [:X => px, :Y => py]; atol=1e-6)
            return observe(bind_utility(m, :U => [0.0 1.0; 2.0 3.0]), observed)
        end
        backends = (DecisionVariableElimination(), DecisionVariableElimination(; atol=1e-9),
                    DecisionVariableElimination(; atol=0.4), ExhaustivePolicySearch(),
                    ExhaustivePolicySearch(; brute_force=true))
        function detail(m, backend)
            try
                optimize(m, backend; atol=1e-6)
                return ""
            catch e
                e isa BayesianNetworks.IndeterminatePosteriorError || rethrow()
                return e.detail
            end
        end

        # (a) P(X = a | Y = b) is about -0.29. DVE returned 3.58, above the largest utility.
        cell = model([1 - 4e-6, 4e-6], [1+9e-7 -9e-7; 0 1], :Y => :b)
        for backend in backends
            @test occursin("posterior cell is negative", detail(cell, backend))
        end
        @test_throws BayesianNetworks.IndeterminatePosteriorError expected_utility(cell,
                                                                                   :D => :act;
                                                                                   atol=1e-6)
        # A version-2 certificate records the same run, so it raises too.
        @test_throws BayesianNetworks.IndeterminatePosteriorError export_dve_certificate(cell;
                                                                                         atol=1e-6,
                                                                                         solution=true)

        # (b) The evidence mass, 4e-7, is within the budget of the normalisation tolerance,
        # `(1 + 1e-6)^3 - 1`: two chance mechanisms and the decision's policy, as in the
        # instantiated network. With `atol = 1e-9` DVE took its budget from that and
        # returned 3.5.
        budget = model([1 - 1e-6, 1e-6], [1+1e-7 -1e-7; 0.5 0.5], :Y => :b)
        for backend in backends
            @test occursin("tolerance budget 3.000003", detail(budget, backend))
        end

        # (c) A loose constancy tolerance is not a budget: `atol = 0.4` raised for a mass of
        # 1e-3 against a "budget" of 0.96. The negative entry is off the evidence.
        clear = model([1 - 1e-3, 1e-3], [1+1e-7 -1e-7; 0.5 0.5], :X => :b)
        for backend in backends
            @test optimize(clear, backend; atol=1e-6).expected_utility == 3.0
        end
    end

    # The rule decides by exact zero patterns and signs, never by enumerating joint states,
    # so check it against the exhaustive search on random diagrams: tolerated negative
    # entries land on rows the evidence selects or rules out, some rows are nearly
    # deterministic so that masses come near the budget, and some diagrams have no
    # evidence. The binary64 run, the exact rerun (called directly) and the search agree on
    # whether the posterior is indeterminate, and on the value when it is not.
    @testset "tolerated negative entries: backends agree on random diagrams" begin
        atol = 1e-6
        function action_free(id, x)
            visited, pending = Set{Symbol}(), [x]
            while !isempty(pending)
                for p in parents(id, variable_id(id, pop!(pending)))
                    is_decision(id, p) && return false
                    name = variable_name(id, p)
                    name in visited || (push!(visited, name); push!(pending, name))
                end
            end
            return true
        end
        function perturbed(rng)
            m = random_influence_model(rng; nchance=rand(rng, 2:4),
                                       ndecision=rand(rng, 1:2), max_info_states=4)
            id = syntax(m)
            for x in chance_names(id)
                t = copy(cpt(kernel(m, x)))
                n = size(t)[end]
                for r in CartesianIndices(size(t)[1:(end - 1)])
                    if rand(rng) < 0.5
                        ε = exp10(-rand(rng, 3:8))
                        row = fill(ε / (n - 1), n)
                        row[rand(rng, 1:n)] = 1 - ε
                        t[r, :] = row
                    end
                    if rand(rng) < 0.15
                        j = rand(rng, 1:n)
                        i = rand(rng, setdiff(1:n, [j]))
                        δ = 0.9 * atol * rand(rng)
                        t[r, i] += t[r, j] + δ
                        t[r, j] = -δ
                    end
                end
                m = bind_cpt(m, x => t; atol)
            end
            free = [x for x in chance_names(id) if action_free(id, x)]
            (isempty(free) || rand(rng) < 0.15) && return m
            observed = shuffle(rng, free)[1:rand(rng, 1:min(2, length(free)))]
            return observe(m, [x => rand(rng, states(id, x)) for x in observed])
        end
        function outcome(solve)
            try
                return (:value, solve().expected_utility)
            catch e
                e isa BayesianNetworks.IndeterminatePosteriorError || rethrow()
                return (:indeterminate, NaN)
            end
        end
        # The total magnitude of the negative entries, and a bound on the total utility.
        negative_mass(m) = sum(sum(x -> max(-x, 0.0), kernel(m, x).table)
                               for x in chance_names(syntax(m)))
        function utility_bound(m)
            id = syntax(m)
            return sum(maximum(abs,
                               utility_table(u,
                                             InfluenceDiagrams._utility_axes(m,
                                                                             utility_id(id,
                                                                                        name))))
                       for (name, u) in m.utilities)
        end
        order = BayesianNetworkInference.MinFill()
        rng = MersenneTwister(20261002)
        seen = Set{Tuple{Symbol,Bool,Bool}}()
        for _ in 1:60
            m = perturbed(rng)
            dve = outcome(() -> optimize(m; atol))
            rerun = outcome(() -> InfluenceDiagrams._exact_rerun(m, order, atol, atol))
            search = outcome(() -> optimize(m, ExhaustivePolicySearch(); atol))
            @test first(dve) == first(rerun) == first(search)
            prior = isempty(evidence(m))
            negative = InfluenceDiagrams._has_negative_entry(m)
            push!(seen, (first(dve), negative, prior))
            first(dve) == first(rerun) == first(search) == :value || continue
            @test isapprox(last(rerun), last(dve); rtol=1e-9, atol=1e-12)
            if prior && negative
                # A prior is exempt, and its joint may hold negative cells. On an
                # information row of negative mass the search, which maximizes the signed
                # sum, takes the worse action, so it can exceed DVE's per-row maximum, by
                # at most four times the utility bound times the negative mass.
                @test last(search) >= last(dve) - 1e-12
                @test last(search) - last(dve) <=
                      4 * 1.01 * utility_bound(m) * negative_mass(m) + 1e-12
            else
                @test isapprox(last(dve), last(search); rtol=1e-9, atol=1e-12)
            end
        end
        # Both outcomes occur, an entry the evidence rules out is answered, and a prior
        # with a negative entry is answered.
        @test (:indeterminate, true, false) in seen
        @test (:value, true, false) in seen
        @test (:value, true, true) in seen
    end

    # Review finding 2: in binary64 a probability row that underflows is rounded so coarsely
    # that it looks non-constant in the action. The run is untrusted once a product of
    # nonzero values falls below `floatmin`, and is repeated exactly, instead of raising
    # `IrregularDiagramError`.
    @testset "an underflowed product sends DVE to the exact rerun" begin
        id = influence_diagram(:X => [:a, :b], :E1 => [:e, :f], :E2 => [:e, :f],
                               :Y => [:y0, :y1, :y2], :D => [:d1, :d2];
                               mechanisms=[:X => (), :E1 => (:X,), :E2 => (:X,),
                                           :Y => (:X, :D)],
                               decisions=[:D => ()], utilities=[:U => :Y])
        y = zeros(2, 2, 3)
        y[1, 1, :] = [0.0, 1.0, 0.0]
        y[1, 2, :] = [0.0, 0.0, 1.0]
        y[2, 1, :] = [0.1, 0.8, 0.1]
        y[2, 2, :] = [0.3, 0.4, 0.3]
        function rare(scale)
            e = [scale 1-scale; 3scale 1-3scale]
            m = bind_cpt(InfluenceDiagramModel(id),
                         [:X => [0.5, 0.5], :E1 => e, :E2 => e, :Y => y])
            return observe(bind_utility(m, :U => [0.0, 1.0, 2.0]), [:E1 => :e, :E2 => :e])
        end
        # The evidence mass is 5 scale^2: 5e-320 here. DVE raised IrregularDiagramError.
        m = rare(1e-160)
        sol = optimize(m)
        exact = optimize(m, DecisionVariableElimination(; stable=true))
        @test sol.diagnostics.exact_fallback && exact.expected_utility == 1.1
        @test sol.expected_utility === exact.expected_utility
        @test policy_table(sol.strategy[:D]) == policy_table(exact.strategy[:D])
        @test optimize(m, ExhaustivePolicySearch()).expected_utility == 1.1
        # Masses from about 1e-322 to 1e-316 failed; the rerun is the stable run exactly.
        for scale in exp10.(range(-161.5, -158; length=15))
            r = rare(scale)
            @test optimize(r).expected_utility ===
                  optimize(r, DecisionVariableElimination(; stable=true)).expected_utility
        end
        # A normal product is trusted and takes no rerun.
        @test !haskey(optimize(rare(1e-100)).diagnostics, :exact_fallback)

        # A product of nonzero values can round straight to 0.0, with no subnormal step:
        # 1e-200 * 1e-200 here. The evidence mass stays normal through the row y2, but the
        # row x1 had a probability of zero in binary64, so its policy entry was the first
        # label instead of the exact maximizer.
        zero_id = influence_diagram(:X => [:x1, :x2], :Y => [:y1, :y2], :E1 => [:e, :f],
                                    :E2 => [:e, :f], :D => [:d1, :d2];
                                    mechanisms=[:X => (), :Y => (:X,), :E1 => (:Y,),
                                                :E2 => (:Y,)],
                                    decisions=[:D => :X], utilities=[:U => (:Y, :D)])
        likelihood = [1e-200 1-1e-200; 0.5 0.5]
        z = bind_cpt(InfluenceDiagramModel(zero_id),
                     [:X => [0.5, 0.5], :Y => [1.0 0.0; 0.0 1.0], :E1 => likelihood,
                      :E2 => likelihood])
        z = observe(bind_utility(z, :U => [0.0 1.0; 2.0 0.0]), [:E1 => :e, :E2 => :e])
        sol = optimize(z)
        exact = optimize(z, DecisionVariableElimination(; stable=true))
        @test sol.diagnostics.exact_fallback
        @test policy_table(sol.strategy[:D]) == policy_table(exact.strategy[:D]) ==
              [:d2, :d1]
        @test sol.expected_utility === exact.expected_utility == 2.0
    end

    # Review finding 5: an intervention leaves the replaced kernel bound under its old
    # reference. Its negative entry is not the model's, and raised a spurious
    # `IndeterminatePosteriorError` both on the exact rerun and under the budget.
    @testset "a kernel an intervention replaced is not the model's" begin
        id = influence_diagram(:A => [:rare, :usual], :B => [:rare, :usual],
                               :W => [:w0, :w1], :D => [:leave, :act];
                               decisions=[:D => ()], utilities=[:Value => :D])
        # An underflowed mass (the exact rerun), and a normal one within the budget.
        for pa in ([1e-200, 1.0], [1e-7, 1 - 1e-7])
            m = bind_cpt(InfluenceDiagramModel(id),
                         [:A => pa, :B => [1e-200, 1.0], :W => [1 + 1e-7, -1e-7]];
                         atol=1e-6)
            m = bind_utility(m, :Value => [-2.0, 3.0])
            intervened = observe(do_intervention(m, :W => :w0),
                                 [:A => :rare, :B => :rare])
            @test optimize(intervened; atol=1e-6).expected_utility == 3.0
            @test optimize(intervened, ExhaustivePolicySearch();
                           atol=1e-6).expected_utility ==
                  3.0
            # Without the intervention the negative entry is the model's.
            kept = observe(m, [:A => :rare, :B => :rare])
            @test_throws BayesianNetworks.IndeterminatePosteriorError optimize(kept;
                                                                               atol=1e-6)
            @test_throws BayesianNetworks.IndeterminatePosteriorError optimize(kept,
                                                                               ExhaustivePolicySearch();
                                                                               atol=1e-6)
        end
    end

    @testset "state counts beyond Int128 are too large" begin
        names = [Symbol("C", i) for i in 1:130]
        id = influence_diagram((x => [:no, :yes] for x in names)..., :D => [:leave, :act];
                               decisions=[:D => ()], utilities=[:U => :D])
        m = bind_cpt(InfluenceDiagramModel(id), [x => [0.5, 0.5] for x in names])
        m = bind_utility(m, :U => [0.0, 1.0])
        @test_throws ModelTooLargeError optimize(m, ExhaustivePolicySearch())
    end
end
