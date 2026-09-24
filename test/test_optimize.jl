@testset "Optimisation: exhaustive search and DVE (Proposition 7)" begin
    @testset "umbrella" begin
        m = umbrella_model()
        ex = optimize(m, ExhaustivePolicySearch())
        dve = optimize(m, DecisionVariableElimination())
        @test ex isa DecisionSolution && dve isa DecisionSolution
        @test ex.expected_utility ≈ 77.0
        @test dve.expected_utility ≈ 77.0
        @test optimize(m).expected_utility ≈ 77.0
        best = deterministic_policy(m, :Umbrella, f -> f == :rainy ? :take : :leave)
        @test ex.strategy[:Umbrella] == best
        @test dve.strategy[:Umbrella] == best
        @test agree_on_reachable(m, ex.strategy, dve.strategy)
        @test ex.diagnostics.nstrategies == 8
        @test dve.diagnostics.order == [:Weather, :Umbrella, :Forecast]
        @test dve.diagnostics.policy_scopes[:Umbrella] == [:Forecast]
        @test dve.diagnostics.evidence_probability ≈ 1
        @test strong_elimination_order(m) == [:Weather, :Umbrella, :Forecast]
        @test occursin("77", sprint(show, dve))
        # installing the solution
        @test expected_utility(set_policy(m, dve.strategy)) ≈ 77.0
        # no information
        noinfo = without_information(m, :Umbrella, :Forecast)
        @test optimize(noinfo).expected_utility ≈ 70.0
        @test optimize(noinfo, ExhaustivePolicySearch()).expected_utility ≈ 70.0
        @test optimize(noinfo).strategy[:Umbrella]() == :leave
        # perfect information
        perfect = with_information(noinfo, :Umbrella, :Weather)
        @test optimize(perfect).expected_utility ≈ 91.0
        @test optimize(perfect, ExhaustivePolicySearch()).expected_utility ≈ 91.0
        # the exhaustive backend refuses large searches
        @test_throws PolicySearchTooLargeError optimize(m,
                                                        ExhaustivePolicySearch(;
                                                                               max_policies=7))
        # brute-force variant
        @test optimize(m, ExhaustivePolicySearch(; brute_force=true)).expected_utility ≈
              77.0
    end

    @testset "umbrella with evidence" begin
        m = observe(umbrella_model(), :Forecast => :rainy)
        ex = optimize(m, ExhaustivePolicySearch())
        dve = optimize(m)
        @test ex.expected_utility ≈ 0.28 * 20 + 0.72 * 70
        @test dve.expected_utility ≈ ex.expected_utility
        @test dve.diagnostics.evidence_probability ≈ 0.25
        @test dve.strategy[:Umbrella](:rainy) == :take
        # evidence on a descendant of the action is refused by DVE
        wet = influence_diagram(:Weather => [:sunny, :rainy], :Umbrella => [:take, :leave],
                                :Wet => [:no, :yes];
                                mechanisms=[:Wet => (:Weather, :Umbrella)],
                                decisions=[:Umbrella => Symbol[]], utilities=[:U => :Wet])
        wm = InfluenceDiagramModel(wet)
        wet = zeros(2, 2, 2)   # (Weather, Umbrella, Wet)
        wet[1, 1, :] = [0.9, 0.1]
        wet[1, 2, :] = [0.8, 0.2]
        wet[2, 1, :] = [0.6, 0.4]
        wet[2, 2, :] = [0.0, 1.0]
        wm = bind_cpt(wm, [:Weather => [0.7, 0.3], :Wet => wet])
        wm = bind_utility(wm, :U => [10.0, 0.0])
        @test optimize(wm).expected_utility ≈
              optimize(wm, ExhaustivePolicySearch()).expected_utility
        @test_throws IrregularDiagramError optimize(observe(wm, :Wet => :no))
    end

    @testset "grazing" begin
        g = reference_grazing_model()
        ex = optimize(g, ExhaustivePolicySearch())
        dve = optimize(g)
        @test ex.expected_utility ≈ dve.expected_utility
        @test ex.diagnostics.nstrategies == 3^9
        @test agree_on_reachable(g, ex.strategy, dve.strategy)
        @test expected_utility(g, dve.strategy) ≈ dve.expected_utility
        @test expected_utility(g, ex.strategy) ≈ ex.expected_utility
        # the optimum beats every fixed action
        for a in (:exclude, :reduce, :maintain)
            @test dve.expected_utility >=
                  expected_utility(g, :GrazingManagement => a) - 1e-9
        end
        @test dve.diagnostics.policy_scopes[:GrazingManagement] ⊆
              [:ClimateForecast, :CurrentVegetation]
    end

    @testset "two-stage sequential decisions" begin
        t = two_stage_model()
        ex = optimize(t, ExhaustivePolicySearch())
        dve = optimize(t)
        @test ex.expected_utility ≈ 21.0
        @test dve.expected_utility ≈ 21.0
        @test ex.strategy[:Test]() == :test
        @test dve.strategy[:Test]() == :test
        @test dve.strategy[:Drill](:test, :pos) == :drill
        @test dve.strategy[:Drill](:test, :neg) == :dont
        @test agree_on_reachable(t, ex.strategy, dve.strategy)
        @test expected_utility(t, dve.strategy) ≈ 21.0
        order = dve.diagnostics.order
        @test findfirst(==(:Drill), order) < findfirst(==(:Test), order)
        @test findfirst(==(:Oil), order) < findfirst(==(:Drill), order)
        @test findfirst(==(:Result), order) > findfirst(==(:Drill), order)
        # a forgetting diagram is refused: Drill no longer observes Test
        forget = without_information(t, :Drill, :Test)
        @test_throws IrregularDiagramError optimize(forget)
        @test optimize(forget, ExhaustivePolicySearch()).expected_utility <= 21.0 + 1e-9
    end

    @testset "random tiny diagrams (SPEC section 56 item 6)" begin
        rng = MersenneTwister(2026)
        matched = 0
        for _ in 1:15
            m = random_influence_model(rng)
            ex = optimize(m, ExhaustivePolicySearch())
            dve = optimize(m)
            @test isapprox(ex.expected_utility, dve.expected_utility; atol=1e-9)
            # the recovered strategies are both optimal
            @test isapprox(expected_utility(m, dve.strategy), ex.expected_utility;
                           atol=1e-9)
            @test isapprox(expected_utility(m, ex.strategy), ex.expected_utility; atol=1e-9)
            @test is_complete(dve.strategy, syntax(m))
            for (d, p) in policies(dve.strategy)
                @test p isa DeterministicPolicy
                @test validate_policy(m, d, p) === nothing
            end
            matched += 1
        end
        @test matched == 15
    end

    @testset "elimination strategies" begin
        g = reference_grazing_model()
        base = optimize(g).expected_utility
        for s in
            (BayesianNetworkInference.MinDegree(), BayesianNetworkInference.AMDOrder(),
             BayesianNetworkInference.ExactTreewidth())
            @test optimize(g, DecisionVariableElimination(; order=s)).expected_utility ≈
                  base
        end
        o = strong_elimination_order(g)
        @test length(o) == nparts(syntax(g), :Variable)
        @test findfirst(==(:GrazingManagement), o) > findfirst(==(:Biodiversity), o)
        @test findfirst(==(:ClimateForecast), o) > findfirst(==(:GrazingManagement), o)
    end

    @testset "optimisation needs a bound model" begin
        m = InfluenceDiagramModel(umbrella_diagram())
        @test_throws MissingKernelError optimize(m)
        @test_throws MissingKernelError optimize(m, ExhaustivePolicySearch())
        m = bind_cpt(m, [:Weather => [0.7, 0.3], :Forecast => [0.7 0.2 0.1; 0.15 0.25 0.6]])
        @test_throws MissingUtilityError optimize(m)
    end
end

@testset "Evidence on an action variable is refused (SPEC section 41)" begin
    m = umbrella_model()

    @testset "observe refuses it at the point of use" begin
        e = try
            observe(m, :Umbrella => :leave)
            nothing
        catch err
            err
        end
        @test e isa EvidenceOnActionError
        @test e.variable == :Umbrella && e.decision == :Umbrella && e.state == :leave
        msg = sprint(showerror, e)
        @test occursin("fix_decision", msg) && occursin("set_policy", msg)
        # the decision operations are the way to pin an action down
        @test expected_utility(fix_decision(m, :Umbrella => :leave)) ≈ 70.0
        # chance variables are still observable
        @test evidence(observe(m, :Forecast => :rainy)) == Dict(:Forecast => :rainy)
    end

    @testset "both backends and expected_utility refuse it" begin
        # evidence smuggled in through the inner BayesModel, bypassing observe
        inner = observe(bayes_model(m), :Umbrella => :leave)
        bad = InfluenceDiagramModel(inner; utilities=bound_utilities(m))
        @test_throws EvidenceOnActionError validate(bad)
        @test_throws EvidenceOnActionError optimize(bad;
                                                    backend=DecisionVariableElimination())
        @test_throws EvidenceOnActionError optimize(bad; backend=ExhaustivePolicySearch())
        @test_throws EvidenceOnActionError expected_utility(bad,
                                                            Strategy(:Umbrella => ConstantPolicy(:leave)))
        # before the fix DVE returned 70.0 with the policy [take, take, take] and
        # exhaustive search 91.59, above the perfect-information optimum of 91
        @test optimize(m).expected_utility ≈ 77.0
        @test optimize(with_information(without_information(m, :Umbrella, :Forecast),
                                        :Umbrella, :Weather)).expected_utility ≈ 91.0
    end
end

@testset "No-forgetting: detection, message and repair (Shachter 1986)" begin
    # Two decisions with no information and no precedence: valid, solvable by
    # enumeration, rejected by decision variable elimination.
    id = influence_diagram(:A => [:a1, :a2], :B => [:b1, :b2], :X => [:x1, :x2];
                           mechanisms=[:X => (:A, :B)],
                           decisions=[:A => Symbol[], :B => Symbol[]],
                           utilities=[:U => :X])
    tab = zeros(2, 2, 2)   # (A, B, X)
    tab[1, 1, :] = [0.9, 0.1]
    tab[1, 2, :] = [0.2, 0.8]
    tab[2, 1, :] = [0.5, 0.5]
    tab[2, 2, :] = [0.1, 0.9]
    m = bind_utility(bind_cpt(InfluenceDiagramModel(id), :X => tab), :U => [0.0, 10.0])

    @testset "validate accepts a limited-memory diagram" begin
        @test validate(syntax(m)) === nothing
        @test validate(m; closed=true, unique_names=true, semantics=true) === nothing
        @test !is_no_forgetting(m)
        @test no_forgetting_arcs(m) == [:B => :A]
        @test no_forgetting_arcs(syntax(m)) == no_forgetting_arcs(m)
        # single-decision and well-formed sequential diagrams have nothing missing
        @test is_no_forgetting(umbrella_model())
        @test is_no_forgetting(two_stage_model())
        @test isempty(no_forgetting_arcs(reference_grazing_diagram()))
        @test no_forgetting_arcs(syntax(without_information(two_stage_model(), :Drill,
                                                            :Test))) == [:Drill => :Test]
    end

    @testset "the solver names the repair" begin
        e = try
            optimize(m)
            nothing
        catch err
            err
        end
        @test e isa IrregularDiagramError
        @test e.decision == :B && e.variables == [:A] && e.what == :information
        msg = sprint(showerror, e)
        @test occursin("no-forgetting", msg)
        @test occursin("with_no_forgetting", msg)
        @test occursin("ExhaustivePolicySearch", msg)
    end

    @testset "with_no_forgetting repairs it and agrees with the oracle" begin
        ex = optimize(m, ExhaustivePolicySearch())
        fixed = with_no_forgetting(m)
        @test is_no_forgetting(fixed)
        @test information_names(syntax(fixed), :B) == [:A]
        @test optimize(fixed).expected_utility ≈ ex.expected_utility ≈ 9.0
        @test agree_on_reachable(fixed, optimize(fixed).strategy,
                                 optimize(fixed, ExhaustivePolicySearch()).strategy)
        # idempotent, and a no-op on a diagram that already has no-forgetting
        @test with_no_forgetting(fixed) == fixed
        @test with_no_forgetting(two_stage_model()) == two_stage_model()
        @test information_names(with_no_forgetting(syntax(m)), :B) == [:A]
        # the policy of a decision whose information set grew is dropped
        withpolicy = with_no_forgetting(fix_decision(m, [:A => :a1, :B => :b1]))
        @test haskey(strategy(withpolicy), :A)
        @test missing_policies(strategy(withpolicy), syntax(withpolicy)) == [:B]
    end

    @testset "repairing the forgetting two-stage diagram" begin
        forget = without_information(two_stage_model(), :Drill, :Test)
        @test_throws IrregularDiagramError optimize(forget)
        repaired = with_no_forgetting(forget)
        @test optimize(repaired).expected_utility ≈
              optimize(repaired, ExhaustivePolicySearch()).expected_utility
        @test optimize(repaired).expected_utility ≈ 21.0
    end
end
