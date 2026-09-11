struct TestBlockSelection{T} <: BayesianNetworkInference.EliminationStrategy
    variables::T
end
function BayesianNetworkInference.elimination_order(
    ::BayesianNetworkInference.FactorGraph, order::TestBlockSelection;
    keep::AbstractVector{Symbol}=Symbol[])
    return copy(order.variables)
end

@testset "DVE block-order contract" begin
    id = influence_diagram(:X => [:no, :yes], :D => [:off, :on];
                           decisions=[:D => ()], utilities=[:U => :D])
    model = bind_utility(bind_cpt(InfluenceDiagramModel(id), :X => [.5, .5]),
                         :U => [0.0, 10.0])
    original = deepcopy(model)
    reference = optimize(model, ExhaustivePolicySearch())
    @test reference.expected_utility == 10.0

    for strategy in (BayesianNetworkInference.MinFill(), BayesianNetworkInference.MinDegree(),
                     BayesianNetworkInference.AMDOrder(), BayesianNetworkInference.ExactTreewidth(),
                     BayesianNetworkInference.UserOrder([:X]), TestBlockSelection([:X]))
        for stable in (false, true)
            solution = decision_elimination(model; order=strategy, stable=stable)
            @test solution.expected_utility == reference.expected_utility
            @test solution.strategy[:D]() == :on
            @test expected_utility(model, solution.strategy) == reference.expected_utility
            @test solution.diagnostics.order == [:X, :D]
        end
    end

    # Summing an action in a chance block previously reported 5 while its policy attained 0.
    for invalid in ([:D, :X], [:X, :X], [:missing], Symbol[], [1])
        strategy = TestBlockSelection(invalid)
        for stable in (false, true)
            @test_throws BayesianNetworkInference.ScopeError decision_elimination(
                model; order=strategy, stable=stable)
        end
        @test_throws BayesianNetworkInference.ScopeError trace_decision_elimination(
            model; order=strategy, include_compilation=true)
    end

    @test_throws BayesianNetworkInference.ScopeError decision_elimination(
        umbrella_model(); order=TestBlockSelection([:Forecast, :Weather]))
    mutated = BayesianNetworkInference.UserOrder([:X])
    push!(mutated.vars, :X)
    @test_throws BayesianNetworkInference.ScopeError decision_elimination(model; order=mutated)
    @test model == original
end
