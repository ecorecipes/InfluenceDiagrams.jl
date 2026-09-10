@testset "Actual exact DVE capture" begin
    diagram = influence_diagram(:H => [:low, :high], :D => [:off, :on];
                                decisions=[:D => :H], utilities=[:U => (:H, :D)])
    model = bind_cpt(InfluenceDiagramModel(diagram), :H => [.25, .75])
    model = bind_utility(model, :U => [0.0 2.0; 4.0 1.0])
    before = deepcopy(model)
    solution, trace = trace_decision_elimination(model)
    @test solution.expected_utility == 3.5
    @test solution.expected_utility == optimize(model, DecisionVariableElimination(stable=true)).expected_utility
    @test trace["format"] == "ecorecipes.dve-execution-trace"
    @test trace["version"] == 1
    @test !haskey(trace, "compilation")
    @test trace["arithmetic"] == "exact-rational-native-v1"
    @test trace["steps"][1]["kind"] == "decision"
    @test trace["steps"][1]["policy"]["values"] == ["on", "off"]
    @test trace["policies"][1]["values"] == ["on", "off"]
    @test trace["result"] == string(reinterpret(UInt64, 3.5); base=16, pad=16)
    @test model == before
    @test_throws BayesianNetworkInference.ScopeError trace_decision_elimination(model; max_entries=1)

    @test trace_decision_elimination(model; max_entries=34)[1].expected_utility == 3.5
    @test_throws BayesianNetworkInference.ScopeError trace_decision_elimination(
        model; max_entries=34, include_compilation=true)
end

@testset "Actual compilation boundary capture" begin
    diagram = influence_diagram(:A => [:low, :high], :B => [:low, :middle, :high],
                                :S => [:low, :high], :D => [:off, :on];
                                mechanisms=[:S => (:A, :B)], decisions=[:D => :S],
                                utilities=[:U => (:S, :D)])
    model = bind_cpt(InfluenceDiagramModel(diagram), :A => [.25, .75])
    model = bind_cpt(model, :B => [.25, .25, .5])
    probabilities = [.125 .25 .375; .5 .625 .75]
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
    @test compiled["source"]["parent_states"] == [["low", "high"], ["low", "middle", "high"]]
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

    functional = bind_utility(model, :U => FunctionUtility([:S, :D],
                                                           (s, d) -> d == :on ? 1.0 : 0.0))
    @test trace_decision_elimination(functional)[1].expected_utility == 1.0
    @test_throws DVEExportError trace_decision_elimination(functional; include_compilation=true)
end

@testset "Compilation captures repeated parent slots before diagonalization" begin
    diagram = influence_diagram(:P => [:low, :high], :C => [:low, :high], :D => [:off, :on];
                                mechanisms=[:C => (:P, :P)], decisions=[:D => :C],
                                utilities=[:U => (:C, :D)])
    model = bind_cpt(InfluenceDiagramModel(diagram), :P => [.25, .75])
    probability = [0.0 .25; .5 1.0]
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
