@testset "Tied values and unreachable policy rows" begin
    id = influence_diagram(:Signal => [:common, :unreachable], :Act => [:off, :on];
                           decisions=[:Act => :Signal], utilities=[:Reward => (:Signal, :Act)])
    model = bind_cpt(InfluenceDiagramModel(id), :Signal => [1.0, 0.0])
    model = bind_utility(model, :Reward => [1.0 1.0; -5.0 9.0])
    for common in (:off, :on), unreachable in (:off, :on)
        policy = deterministic_policy(model, :Act,
                                      s -> s == :common ? common : unreachable)
        @test validate_policy(model, :Act, policy) === nothing
        strategy_ = Strategy(:Act => policy)
        @test expected_utility(model, strategy_) == 1.0
        @test expected_utility(model, strategy_; stable=true) == 1.0
    end
    solution, trace = trace_decision_elimination(model)
    @test solution.expected_utility == 1.0
    @test solution.strategy[:Act](:common) == :off
    @test trace["policies"][1]["scope"] == ["Signal"]
    @test length(trace["policies"][1]["values"]) == 2
    @test optimize(model, ExhaustivePolicySearch()).expected_utility == solution.expected_utility
end

@testset "Downstream evidence requires policy-specific denominators" begin
    id = influence_diagram(:Act => [:avoid, :seek], :Outcome => [:no, :yes];
                           mechanisms=[:Outcome => :Act], decisions=[:Act => ()],
                           utilities=[:Reward => :Act])
    model = bind_cpt(InfluenceDiagramModel(id), :Outcome => [1.0 0.0; 0.5 0.5])
    model = observe(bind_utility(model, :Reward => [10.0, 2.0]), :Outcome => :yes)
    @test validate(model; closed=true, semantics=true) === nothing
    @test is_no_forgetting(model)
    @test_throws IrregularDiagramError optimize(model)
    @test_throws IrregularDiagramError optimize(model, DecisionVariableElimination(stable=true))
    @test_throws BayesianNetworks.ImpossibleEvidenceError expected_utility(
        model, Strategy(:Act => ConstantPolicy(:avoid)))
    for backend in (ExhaustivePolicySearch(), ExhaustivePolicySearch(brute_force=true),
                    ExhaustivePolicySearch(stable=true))
        solution = optimize(model, backend)
        @test solution.expected_utility == 2.0
        @test solution.strategy[:Act]() == :seek
        @test expected_utility(model, solution.strategy) == solution.expected_utility
    end
    prospective = unobserve(model)
    @test optimize(prospective).expected_utility == 10.0
    @test optimize(prospective).strategy[:Act]() == :avoid
    impossible = bind_cpt(model, :Outcome => [1.0 0.0; 1.0 0.0])
    for backend in (ExhaustivePolicySearch(), ExhaustivePolicySearch(brute_force=true),
                    ExhaustivePolicySearch(stable=true))
        @test_throws BayesianNetworks.ImpossibleEvidenceError optimize(impossible, backend)
    end
end
