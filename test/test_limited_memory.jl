@testset "Forgetting private information changes the optimum" begin
    actions, guesses, weather = [:quiet, :signal], [:zero, :one], [:zero, :one]
    function exact_value(probabilities, first, second; recall=false)
        return sum(probabilities[w] *
                   ((second[first[w], recall ? w : 1] == w ? 1 : 0) -
                    2 * (first[w] == 2)) for w in 1:2)
    end
    function exact_optimum(probabilities; recall=false)
        contexts = recall ? 4 : 2
        return maximum(exact_value(probabilities, first, reshape(collect(second), 2, :); recall)
                       for first in Iterators.product(1:2, 1:2)
                       for second in Iterators.product(ntuple(_ -> 1:2, contexts)...))
    end
    for prior in (1//4, 1//2, 3//4)
        probabilities = [prior, 1 - prior]
        diagram = influence_diagram(:Weather => weather, :SignalAction => actions, :Guess => guesses;
                                    decisions=[:SignalAction => :Weather, :Guess => :SignalAction],
                                    utilities=[:Cost => :SignalAction, :Reward => (:Weather, :Guess)])
        model = bind_cpt(InfluenceDiagramModel(diagram), :Weather => Float64.(probabilities))
        model = bind_utility(model, [:Cost => [0.0, -2.0], :Reward => [1.0 0.0; 0.0 1.0]])
        before = deepcopy(model)
        @test validate(model; closed=true, semantics=true, unique_names=true) === nothing
        @test no_forgetting_arcs(model) == [:Guess => :Weather]
        @test_throws IrregularDiagramError optimize(model)
        original = exact_optimum(probabilities)
        @test original == max(prior, 1 - prior)
        for backend in (ExhaustivePolicySearch(), ExhaustivePolicySearch(brute_force=true),
                        ExhaustivePolicySearch(stable=true))
            result = optimize(model, backend)
            @test result.expected_utility ≈ Float64(original)
            first = [findfirst(==(result.strategy[:SignalAction](state)), actions) for state in weather]
            second = reshape([findfirst(==(result.strategy[:Guess](action)), guesses) for action in actions], 2, 1)
            @test exact_value(probabilities, first, second) == original
        end
        recalled = with_no_forgetting(model)
        @test is_no_forgetting(recalled)
        @test exact_optimum(probabilities; recall=true) == 1
        for backend in (DecisionVariableElimination(), ExhaustivePolicySearch())
            result = optimize(recalled, backend)
            @test result.expected_utility ≈ 1.0
            @test result.expected_utility > Float64(original)
            @test expected_utility(recalled, result.strategy) ≈ 1.0
        end
        @test model == before
        @test information_names(syntax(model), :Guess) == [:SignalAction]
        installed = set_policy(model, Strategy(:SignalAction => ConstantPolicy(:quiet),
                                               :Guess => ConstantPolicy(:zero)))
        expanded = with_no_forgetting(installed)
        @test haskey(strategy(expanded), :SignalAction)
        @test !haskey(strategy(expanded), :Guess)
        @test haskey(strategy(installed), :Guess)
    end
end
