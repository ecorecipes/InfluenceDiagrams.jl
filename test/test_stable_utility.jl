@testset "Stable utility accumulation" begin
    diagram = influence_diagram(:H => [:low, :high], :D1 => [:a, :b], :D2 => [:a, :b];
                                decisions=[:D1 => (), :D2 => :D1],
                                utilities=[:Swing => :H, :Offset => ()])
    model = bind_cpt(InfluenceDiagramModel(diagram), :H => [0.5, 0.5])
    model = bind_utility(model, [:Swing => [1e16, -1e16], :Offset => 1.0])
    strategy = Strategy(:D1 => ConstantPolicy(:a), :D2 => ConstantPolicy(:a))
    @test expected_utility(model, strategy) == 0.0
    @test expected_utility(model, strategy; stable=true) == 1.0
    @test optimize(model, ExhaustivePolicySearch()).expected_utility == 0.0
    stable = optimize(model, ExhaustivePolicySearch(; stable=true))
    @test stable.expected_utility == 1.0
    @test stable.diagnostics.method == :stable_brute_force
    @test expected_utility(model, stable.strategy; stable=true) == 1.0
    @test ExhaustivePolicySearch(10, true).stable == false

    rare = influence_diagram(:A => [:rare, :usual], :B => [:rare, :usual],
                             :D => [:leave, :act];
                             decisions=[:D => ()], utilities=[:Value => :D])
    observed = bind_cpt(InfluenceDiagramModel(rare),
                        [:A => [1e-200, 1.0], :B => [1e-200, 1.0]])
    observed = bind_utility(observed, :Value => [-2.0, 3.0])
    observed = observe(observed, [:A => :rare, :B => :rare])
    @test expected_utility(observed, :D => :act; stable=true) ≈ 3.0
    @test optimize(observed, ExhaustivePolicySearch(; stable=true)).expected_utility ≈ 3.0
    impossible = observe(bind_cpt(observed, :A => [0.0, 1.0]), :A => :rare)
    @test_throws InfluenceDiagrams.BayesianNetworks.ImpossibleEvidenceError expected_utility(impossible,
                                                                                             :D => :act;
                                                                                             stable=true)
    @test_throws InfluenceDiagrams.BayesianNetworks.ModelTooLargeError expected_utility(model,
                                                                                        strategy;
                                                                                        stable=true,
                                                                                        max_states=1)

    umbrella = umbrella_model()
    solution = optimize(umbrella)
    @test expected_utility(umbrella, solution.strategy; stable=true) ≈
          expected_utility(umbrella, solution.strategy)
    @test optimize(umbrella, ExhaustivePolicySearch(; stable=true)).expected_utility ≈
          solution.expected_utility

    conditional = influence_diagram(:D => [:blocked, :allowed], :Y => [:yes, :no];
                                    mechanisms=[:Y => :D], decisions=[:D => ()],
                                    utilities=[:Value => :D])
    conditional = bind_cpt(InfluenceDiagramModel(conditional), :Y => [0.0 1.0; 1.0 0.0])
    conditional = observe(bind_utility(conditional, :Value => [100.0, 2.0]), :Y => :yes)
    for backend in (ExhaustivePolicySearch(), ExhaustivePolicySearch(; brute_force=true),
                    ExhaustivePolicySearch(; stable=true))
        supported = optimize(conditional, backend)
        @test supported.expected_utility == 2.0
        @test supported.strategy[:D]() == :allowed
        unsupported = bind_cpt(conditional, :Y => [0.0 1.0; 0.0 1.0])
        @test_throws InfluenceDiagrams.BayesianNetworks.ImpossibleEvidenceError optimize(unsupported,
                                                                                         backend)
    end
    nonfinite = observe(bind_utility(model, :Swing => [Inf, 0.0]), :H => :high)
    @test_throws UtilityScopeError expected_utility(nonfinite, strategy; stable=true)
end
