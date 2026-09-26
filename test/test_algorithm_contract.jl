@testset "Tied values and unreachable policy rows" begin
    id = influence_diagram(:Signal => [:common, :unreachable], :Act => [:off, :on];
                           decisions=[:Act => :Signal],
                           utilities=[:Reward => (:Signal, :Act)])
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
    @test optimize(model, ExhaustivePolicySearch()).expected_utility ==
          solution.expected_utility
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
    @test_throws IrregularDiagramError optimize(model,
                                                DecisionVariableElimination(; stable=true))
    @test_throws BayesianNetworks.ImpossibleEvidenceError expected_utility(model,
                                                                           Strategy(:Act => ConstantPolicy(:avoid)))
    for backend in (ExhaustivePolicySearch(), ExhaustivePolicySearch(; brute_force=true),
                    ExhaustivePolicySearch(; stable=true))
        solution = optimize(model, backend)
        @test solution.expected_utility == 2.0
        @test solution.strategy[:Act]() == :seek
        @test expected_utility(model, solution.strategy) == solution.expected_utility
    end
    prospective = unobserve(model)
    @test optimize(prospective).expected_utility == 10.0
    @test optimize(prospective).strategy[:Act]() == :avoid
    impossible = bind_cpt(model, :Outcome => [1.0 0.0; 1.0 0.0])
    for backend in (ExhaustivePolicySearch(), ExhaustivePolicySearch(; brute_force=true),
                    ExhaustivePolicySearch(; stable=true))
        @test_throws BayesianNetworks.ImpossibleEvidenceError optimize(impossible, backend)
    end
end

@testset "One ImpossibleEvidenceError binding for zero evidence mass (ADR 0012)" begin
    @test InfluenceDiagrams.ImpossibleEvidenceError ===
          BayesianNetworks.ImpossibleEvidenceError
    @test InfluenceDiagrams.ImpossibleEvidenceError ===
          BayesianNetworkInference.ImpossibleEvidenceError
    @test :ImpossibleEvidenceError in names(InfluenceDiagrams)
    # `using` this package alone, or together with the two that also export the name,
    # binds it once and without ambiguity.
    for packages in (:(using InfluenceDiagrams),
                     :(using InfluenceDiagrams, BayesianNetworks, BayesianNetworkInference))
        fresh = Module()
        Core.eval(fresh, packages)
        @test Core.eval(fresh, :ImpossibleEvidenceError) ===
              BayesianNetworks.ImpossibleEvidenceError
    end

    id = influence_diagram(:Weather => [:dry, :wet], :Forecast => [:sunny, :rainy],
                           :Act => [:stay, :go]; mechanisms=[:Forecast => :Weather],
                           decisions=[:Act => :Forecast],
                           utilities=[:Payoff => (:Weather, :Act)])
    model = bind_cpt(InfluenceDiagramModel(id),
                     [:Weather => [1.0, 0.0], :Forecast => [1.0 0.0; 0.2 0.8]])
    # P(Forecast = rainy) = 1.0 * 0.0 + 0.0 * 0.8 = 0 under every strategy. No action is
    # a causal ancestor of the evidence, so decision elimination reaches its mass check
    # rather than stopping at IrregularDiagramError.
    model = observe(bind_utility(model, :Payoff => [2.0 1.0; -3.0 4.0]),
                    :Forecast => :rainy)
    @test validate(model; closed=true, semantics=true) === nothing
    σ = Strategy(:Act => ConstantPolicy(:go))
    value_table = ExhaustivePolicySearch()
    brute_force = ExhaustivePolicySearch(; brute_force=true)
    network = instantiate(model, σ)
    @test evidence(network) == Dict(:Forecast => :rainy)
    entry_points = ["optimize, decision elimination" => () -> optimize(model),
                    "optimize, exhaustive value table" => () -> optimize(model, value_table),
                    "optimize, exhaustive brute force" => () -> optimize(model, brute_force),
                    "expected_utility" => () -> expected_utility(model, σ),
                    "infer on instantiate" => () -> BayesianNetworkInference.infer(network,
                                                                                   :Weather)]
    @testset "$label" for (label, call) in entry_points
        err = try
            call()
            nothing
        catch e
            e
        end
        @test typeof(err) === InfluenceDiagrams.ImpossibleEvidenceError
        @test err.evidence == Dict(:Forecast => :rainy)
    end
end
