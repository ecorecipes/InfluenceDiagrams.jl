@testset "Schema" begin
    sj = schema_json(SchInfluenceDiagram)
    names_of(key) = Set(String[d["name"] for d in sj[key]])
    @test names_of("Ob") ==
          Set(["Variable", "State", "Mechanism", "Input", "Decision", "InformationInput",
               "Utility", "UtilityInput", "DecisionPrecedence"])
    @test names_of("Hom") ==
          Set(["state_variable", "target", "input_mechanism", "input_variable",
               "decision_variable", "information_decision", "information_variable",
               "utility_node", "utility_variable", "earlier", "later"])
    @test names_of("AttrType") == Set(["Label", "Position", "Ref"])
    @test names_of("Attr") ==
          Set(["variable_name", "space_ref", "state_name", "state_position",
               "mechanism_name", "kernel_ref", "input_position", "decision_name",
               "utility_name", "utility_ref", "information_position", "utility_position"])
    @test isempty(sj["equations"])
    homs = Dict(d["name"] => (d["dom"], d["codom"]) for d in sj["Hom"])
    @test homs["decision_variable"] == ("Decision", "Variable")
    @test homs["information_decision"] == ("InformationInput", "Decision")
    @test homs["information_variable"] == ("InformationInput", "Variable")
    @test homs["utility_node"] == ("UtilityInput", "Utility")
    @test homs["utility_variable"] == ("UtilityInput", "Variable")
    @test homs["earlier"] == ("DecisionPrecedence", "Decision")
    @test homs["later"] == ("DecisionPrecedence", "Decision")
    attrs = Dict(d["name"] => (d["dom"], d["codom"]) for d in sj["Attr"])
    @test attrs["information_position"] == ("InformationInput", "Position")
    @test attrs["utility_position"] == ("UtilityInput", "Position")
    @test attrs["utility_ref"] == ("Utility", "Ref")
    @test schema_json(InfluenceDiagram) == sj

    @testset "matches the Lean-emitted JSON" begin
        # proofs/schemas/influence_diagram.schema.json is emitted by the Lean project
        # (`lake exe emit_schema`); the comparison ignores the "version" block.
        strip_version(x) = filter(kv -> kv.first != :version,
                                  copy(JSON3.read(JSON3.write(x))))
        lean_file = joinpath(@__DIR__, "..", "proofs", "schemas",
                             "influence_diagram.schema.json")
        @test isfile(lean_file)
        lean = strip_version(JSON3.read(read(lean_file, String)))
        julia = strip_version(schema_json(SchInfluenceDiagram))
        @test lean == julia
    end

    @testset "types" begin
        @test InfluenceDiagram <: AbstractInfluenceDiagram
        @test InfluenceDiagram <: AbstractBayesNet
        @test InfluenceDiagram == InfluenceDiagramUntyped{Symbol,Int,KernelRef}
        id = InfluenceDiagram()
        @test nparts(id, :Decision) == 0
        @test nparts(id, :Variable) == 0
    end

    @testset "migration from and to BayesNet" begin
        bn = BayesianNetworks.reference_habitat_bn()
        id = InfluenceDiagram(bn)
        @test nparts(id, :Variable) == nparts(bn, :Variable)
        @test nparts(id, :Input) == nparts(bn, :Input)
        @test nparts(id, :Decision) == 0
        @test BayesNet(id) == bn
        add_decision!(id, :GrazingPressure)
        @test nparts(id, :Decision) == 1
        @test canonicalize(BayesNet(id)) == canonicalize(bn)
    end
end
