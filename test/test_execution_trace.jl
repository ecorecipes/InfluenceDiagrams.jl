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
    @test trace["arithmetic"] == "exact-rational-native-v1"
    @test trace["steps"][1]["kind"] == "decision"
    @test trace["steps"][1]["policy"]["values"] == ["on", "off"]
    @test trace["policies"][1]["values"] == ["on", "off"]
    @test trace["result"] == string(reinterpret(UInt64, 3.5); base=16, pad=16)
    @test model == before
    @test_throws BayesianNetworkInference.ScopeError trace_decision_elimination(model; max_entries=1)
end
