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

    # The 6 diagram mutations of BayesianNetworks.jl's `proofs/scripts/check_records.jl`,
    # which the proved Lean decoder (`Finite/DVE/JsonRecords.lean`) rejects, built inline
    # from the umbrella diagram. The reader is BayesianNetworks' `_parse_acset`, which checks
    # the body against `SchInfluenceDiagram`; the last is a well-shaped document of an
    # invalid diagram, which `validate` reports, as the Lean check does.
    @testset "the acset body is checked against the schema" begin
        base = json_influence_diagram(umbrella_diagram())
        function mutated(f!)
            d = JSON3.read(base, Dict{String,Any})
            f!(d["acset"])
            return JSON3.write(d)
        end
        function message(str)
            try
                parse_json_influence_diagram(str)
            catch e
                e isa BayesianNetworks.FormatError && return e.message
                rethrow()
            end
            return error("the document was accepted")
        end
        rejected = [(a -> delete!(a, "DecisionPrecedence"),
                     ["InfluenceDiagram", "missing the table \"DecisionPrecedence\""]),
                    (a -> (a["InformationInput"][1]["information_variable"] = 9),
                     ["InformationInput row 1", "column \"information_variable\"", "1:3"]),
                    (a -> delete!(a["Utility"][1], "utility_ref"),
                     ["Utility row 1", "missing the column \"utility_ref\""]),
                    (a -> (a["Decision"][1]["decision_name"] = 3),
                     ["Decision row 1", "column \"decision_name\" must be a string"]),
                    (a -> (a["InformationInput"][1]["information_position"] = 0),
                     ["InformationInput row 1", "column \"information_position\"",
                      "one-based"])]
        for (f!, fragments) in rejected
            msg = message(mutated(f!))
            for fragment in fragments
                @test occursin(fragment, msg)
            end
        end
        # Read, then reported by `validate`: the action variable is also a mechanism target.
        both = parse_json_influence_diagram(mutated(a -> (a["Mechanism"][1]["target"] = a["Decision"][1]["decision_variable"])))
        @test any(e -> e isa DecisionUniquenessError && e.reason == :has_mechanism,
                  validation_errors(both))
        # The influence-diagram columns come from `SchInfluenceDiagram`, as `idColumns`.
        cols(ob) = [c => kind
                    for (c, (kind, _)) in
                        BayesianNetworks._json_columns(SchInfluenceDiagram, ob)]
        @test cols(:Decision) ==
              [:_id => :id, :decision_variable => :hom, :decision_name => :label]
        @test cols(:Utility) == [:_id => :id, :utility_name => :label, :utility_ref => :ref]
        @test cols(:DecisionPrecedence) == [:_id => :id, :earlier => :hom, :later => :hom]
        # What Julia writes is still read, a precedence row included.
        t = two_stage_diagram()
        add_precedence!(t, :Test => :Drill)
        @test parse_json_influence_diagram(json_influence_diagram(t)) == t
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
