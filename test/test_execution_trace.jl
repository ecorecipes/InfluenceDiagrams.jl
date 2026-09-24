@testset "Actual exact DVE capture" begin
    diagram = influence_diagram(:H => [:low, :high], :D => [:off, :on];
                                decisions=[:D => :H], utilities=[:U => (:H, :D)])
    model = bind_cpt(InfluenceDiagramModel(diagram), :H => [0.25, 0.75])
    model = bind_utility(model, :U => [0.0 2.0; 4.0 1.0])
    before = deepcopy(model)
    solution, trace = trace_decision_elimination(model)
    @test solution.expected_utility == 3.5
    @test solution.expected_utility ==
          optimize(model, DecisionVariableElimination(; stable=true)).expected_utility
    @test trace["format"] == "ecorecipes.dve-execution-trace"
    @test trace["version"] == 1
    @test !haskey(trace, "compilation")
    @test trace["arithmetic"] == "exact-rational-native-v1"
    @test trace["steps"][1]["kind"] == "decision"
    @test trace["steps"][1]["policy"]["values"] == ["on", "off"]
    @test trace["policies"][1]["values"] == ["on", "off"]
    @test trace["result"] == string(reinterpret(UInt64, 3.5); base=16, pad=16)
    @test model == before
    @test_throws BayesianNetworkInference.ScopeError trace_decision_elimination(model;
                                                                                max_entries=1)

    @test trace_decision_elimination(model; max_entries=34)[1].expected_utility == 3.5
    @test_throws BayesianNetworkInference.ScopeError trace_decision_elimination(model;
                                                                                max_entries=34,
                                                                                include_compilation=true)
end

@testset "Actual compilation boundary capture" begin
    diagram = influence_diagram(:A => [:low, :high], :B => [:low, :middle, :high],
                                :S => [:low, :high], :D => [:off, :on];
                                mechanisms=[:S => (:A, :B)], decisions=[:D => :S],
                                utilities=[:U => (:S, :D)])
    model = bind_cpt(InfluenceDiagramModel(diagram), :A => [0.25, 0.75])
    model = bind_cpt(model, :B => [0.25, 0.25, 0.5])
    probabilities = [0.125 0.25 0.375; 0.5 0.625 0.75]
    source_table = cat(probabilities, 1 .- probabilities; dims=3)
    model = bind_cpt(model, :S => source_table)
    model = bind_utility(model, :U => [0.0 10.0; 8.0 -3.0])
    original = deepcopy(model)
    solution, trace = trace_decision_elimination(model; include_compilation=true)
    @test solution.expected_utility == trace_decision_elimination(model)[1].expected_utility
    @test trace["version"] == 2
    compilation = trace["compilation"]
    @test compilation["format"] == "ecorecipes.dve-compilation"
    @test compilation["table_layout"] == "first-axis-fastest"
    @test compilation["kernel_layout"] == "outputs-first"
    @test length(compilation["inputs"]) == length(trace["inputs"])
    compiled = only(filter(row -> row["name"] == "S", compilation["inputs"]))
    @test compiled["source"]["parents"] == ["A", "B"]
    @test compiled["source"]["parent_states"] ==
          [["low", "high"], ["low", "middle", "high"]]
    @test compiled["source"]["child_states"] == ["low", "high"]
    @test compiled["source"]["cpt"]["shape"] == [2, 3, 2]
    @test compiled["source"]["kernel"]["shape"] == [2, 2, 3]
    @test compiled["effective"]["scope"] == ["A", "B", "S"]
    @test compiled["effective"]["table"]["shape"] == [2, 3, 2]
    bits = value -> string(reinterpret(UInt64, value); base=16, pad=16)
    @test compiled["source"]["cpt"]["values"] == bits.(vec(source_table))
    @test compiled["effective"]["table"]["values"] == bits.(vec(source_table))
    @test compiled["source"]["kernel"]["values"] == bits.(vec(kernel(model, :S).table))
    compiled["source"]["cpt"]["values"][1] = bits(1.0)
    @test cpt(kernel(model, :S)) == source_table
    @test model == original

    functional = bind_utility(model,
                              :U => FunctionUtility([:S, :D],
                                                    (s, d) -> d == :on ? 1.0 : 0.0))
    @test trace_decision_elimination(functional)[1].expected_utility == 1.0
    @test_throws DVEExportError trace_decision_elimination(functional;
                                                           include_compilation=true)
end

@testset "Compilation captures repeated parent slots before diagonalization" begin
    diagram = influence_diagram(:P => [:low, :high], :C => [:low, :high], :D => [:off, :on];
                                mechanisms=[:C => (:P, :P)], decisions=[:D => :C],
                                utilities=[:U => (:C, :D)])
    model = bind_cpt(InfluenceDiagramModel(diagram), :P => [0.25, 0.75])
    probability = [0.0 0.25; 0.5 1.0]
    model = bind_cpt(model, :C => cat(probability, 1 .- probability; dims=3))
    model = bind_utility(model, :U => [0.0 1.0; 1.0 0.0])
    _, trace = trace_decision_elimination(model; include_compilation=true)
    row = only(filter(input -> input["name"] == "C", trace["compilation"]["inputs"]))
    @test row["source"]["parents"] == ["P", "P"]
    @test row["source"]["cpt"]["shape"] == [2, 2, 2]
    @test row["effective"]["scope"] == ["P", "C"]
    @test row["effective"]["table"]["shape"] == [2, 2]
    @test row["effective"]["table"]["values"] ==
          ["0000000000000000", "3ff0000000000000", "3ff0000000000000", "0000000000000000"]
end

@testset "Perfect recall does not reveal hidden chance variables" begin
    diagram = influence_diagram(:Hidden => [:zero, :one], :First => [:left, :right],
                                :Guess => [:zero, :one];
                                decisions=[:First => (), :Guess => :First],
                                utilities=[:Reward => (:Hidden, :Guess)])
    model = bind_cpt(InfluenceDiagramModel(diagram), :Hidden => [0.5, 0.5])
    model = bind_utility(model, :Reward => [1.0 0.0; 0.0 1.0])
    @test is_no_forgetting(model)
    @test information_names(syntax(model), :Guess) == [:First]
    solution, trace = trace_decision_elimination(model)
    @test solution.expected_utility == 0.5
    @test optimize(model, ExhaustivePolicySearch(; stable=true)).expected_utility == 0.5
    @test expected_utility(model, solution.strategy; stable=true) == 0.5
    @test trace["steps"][1]["kind"] == "chance"
    @test trace["steps"][1]["variable"] == "Hidden"
    @test all(!("Hidden" in policy["scope"]) for policy in trace["policies"])
    @test all(validate_policy(model, name, policy) === nothing
              for (name, policy) in policies(solution.strategy))

    informed = with_information(model, :Guess, :Hidden)
    informed_solution, informed_trace = trace_decision_elimination(informed)
    @test is_no_forgetting(informed)
    @test informed_solution.expected_utility == 1.0
    @test optimize(informed, ExhaustivePolicySearch(; stable=true)).expected_utility == 1.0
    @test first(informed_trace["steps"])["decision"] == "Guess"
    @test expected_value_of_information(model, :Hidden, :Guess;
                                        backend=DecisionVariableElimination(; stable=true)) ==
          0.5

    conditioned = observe(model, :Hidden => :zero)
    conditioned_solution, conditioned_trace = trace_decision_elimination(conditioned)
    @test conditioned_solution.expected_utility == 1.0
    @test conditioned_solution.diagnostics.evidence_probability == 0.5
    @test conditioned_trace["final"]["probability"]["values"] ==
          [Dict("numerator" => "1", "denominator" => "2")]
    @test all(step["variable"] != "Hidden" for step in conditioned_trace["steps"])
    @test information_names(syntax(conditioned), :Guess) == [:First]
    @test expected_utility(conditioned, conditioned_solution.strategy; stable=true) == 1.0
    impossible = observe(bind_cpt(model, :Hidden => [1.0, 0.0]), :Hidden => :one)
    @test_throws BayesianNetworks.ImpossibleEvidenceError trace_decision_elimination(impossible)
end
