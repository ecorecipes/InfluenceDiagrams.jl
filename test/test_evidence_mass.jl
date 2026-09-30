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

        # A positive, normal mass that is within the tolerance budget of zero.
        budget = bind_utility(bind_cpt(base,
                                       [:X => [1 - 1e-6, 1e-6],
                                        :Y => [1+1e-7 -1e-7; 0.5 0.5]]; atol=1e-6),
                              util)
        budget = observe(budget, :X => :b)
        @test_throws BayesianNetworks.IndeterminatePosteriorError optimize(budget;
                                                                           atol=1e-6)

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

    @testset "state counts beyond Int128 are too large" begin
        names = [Symbol("C", i) for i in 1:130]
        id = influence_diagram((x => [:no, :yes] for x in names)..., :D => [:leave, :act];
                               decisions=[:D => ()], utilities=[:U => :D])
        m = bind_cpt(InfluenceDiagramModel(id), [x => [0.5, 0.5] for x in names])
        m = bind_utility(m, :U => [0.0, 1.0])
        @test_throws ModelTooLargeError optimize(m, ExhaustivePolicySearch())
    end
end
