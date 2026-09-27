@testset "Serialization and canonical forms" begin
    id = reference_grazing_diagram()
    set_subpart!(id, 1, :utility_ref, NamedRef("benefit"))
    add_precedence!(two_stage_diagram(), :Test => :Drill)

    @testset "JSON round trip" begin
        s = json_influence_diagram(id)
        obj = JSON3.read(s)
        @test obj[:format] == "influence-diagram-acset"
        @test obj[:schema_version] == "0.1"
        @test haskey(obj[:acset], :Decision)
        back = parse_json_influence_diagram(s)
        @test back isa InfluenceDiagram
        @test back == id
        @test utility_ref(back, 1) == NamedRef("benefit")
        path = joinpath(mktempdir(), "grazing.json")
        @test write_json_influence_diagram(path, id) == path
        @test read_json_influence_diagram(path) == id
        @test_throws BayesianNetworks.FormatError parse_json_influence_diagram("[]")
        @test_throws BayesianNetworks.FormatError parse_json_influence_diagram("{\"format\":\"bayesnet-acset\",\"schema_version\":\"0.1\",\"acset\":{}}")
        # Text that is not JSON is a FormatError too, not JSON3's ArgumentError.
        @test_throws BayesianNetworks.FormatError parse_json_influence_diagram("not json")
        bad = joinpath(mktempdir(), "not.json")
        write(bad, "not json")
        @test_throws BayesianNetworks.FormatError read_json_influence_diagram(bad)
    end

    @testset "canonicalize and is_isomorphic" begin
        t = two_stage_diagram()
        add_precedence!(t, :Test => :Drill)
        # the same diagram built in another order
        t2 = influence_diagram(:Drill => [:drill, :dont], :Result => [:pos, :neg, :none],
                               :Test => [:test, :skip], :Oil => [:dry, :wet];
                               mechanisms=[:Result => (:Oil, :Test)],
                               decisions=[:Drill => (:Test, :Result), :Test => Symbol[]],
                               utilities=[:TestCost => :Test, :Payoff => (:Oil, :Drill)],
                               precedence=[:Test => :Drill])
        @test t != t2
        @test canonicalize(t) == canonicalize(t2)
        @test is_isomorphic(t, t2)
        @test !is_isomorphic(t, two_stage_diagram())   # no precedence row
        @test canonicalize(t) == canonicalize(canonicalize(t))
        # renamed decision: not isomorphic
        t3 = deepcopy(t)
        set_subpart!(t3, 1, :decision_name, :Other)
        @test !is_isomorphic(t, t3)
    end
end
