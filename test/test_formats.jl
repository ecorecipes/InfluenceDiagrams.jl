@testset "Formats bridge" begin
    @testset "fixtures match the examples" begin
        u = read_influence_diagram(fixture_path("dne/umbrella.dne"))
        @test u isa InfluenceDiagramModel
        @test u ≈ umbrella_model()
        @test extras(u)[:format] == :dne
        @test extras(u)[:titles][:Umbrella] == "Take umbrella?"
        @test optimize(u).expected_utility ≈ 77.0
        ux = read_influence_diagram(fixture_path("xdsl/umbrella.xdsl"))
        @test ux ≈ umbrella_model()
        g = read_influence_diagram(fixture_path("dne/grazing_reference_id.dne"))
        @test g ≈ reference_grazing_model()
        @test information_names(syntax(g), :GrazingManagement) ==
              [:ClimateForecast, :CurrentVegetation]
        gx = read_influence_diagram(fixture_path("xdsl/grazing_reference_id.xdsl"))
        @test gx ≈ reference_grazing_model()
        @test length(extras(gx)[:mau]) == 1
        @test optimize(g).expected_utility ≈
              optimize(reference_grazing_model()).expected_utility
    end

    @testset "NetworkIR" begin
        m = umbrella_model()
        ir = NetworkIR(m)
        @test ir isa NetworkIR
        @test [v.id for v in ir.variables] == [:Weather, :Forecast, :Umbrella, :U]
        kinds = Dict(v.id => v.kind for v in ir.variables)
        @test kinds[:Umbrella] == BayesianNetworkFormats.DecisionNode
        @test kinds[:U] == BayesianNetworkFormats.UtilityNode
        @test kinds[:Weather] == BayesianNetworkFormats.ChanceNode
        vu = BayesianNetworkFormats.variable(ir, :U)
        @test vu.parents == [:Weather, :Umbrella]
        @test vu.table == [20.0 100.0; 70.0 0.0]
        vd = BayesianNetworkFormats.variable(ir, :Umbrella)
        @test vd.parents == [:Forecast] && vd.table === nothing
        @test BayesianNetworkFormats.variable(ir, :Forecast).table ==
              [0.7 0.2 0.1; 0.15 0.25 0.6]
        @test InfluenceDiagramModel(ir) ≈ m
        # unbound tables become nothing
        ir0 = NetworkIR(InfluenceDiagramModel(umbrella_diagram()))
        @test all(v.table === nothing for v in ir0.variables)
        # MAU weights must be one
        bad = BayesianNetworkFormats.NetworkIR("x", ir.variables;
                                               mau=[BayesianNetworkFormats.MAUNode(:M, [:U],
                                                                                   [0.5])])
        @test_throws UnsupportedAggregationError InfluenceDiagramModel(bad)
    end

    @testset "round trips" begin
        dir = mktempdir()
        for (name, m) in
            ("umbrella" => umbrella_model(), "grazing" => reference_grazing_model())
            for ext in ("dne", "xdsl", "net")
                path = joinpath(dir, "$name.$ext")
                @test write_influence_diagram(path, m) == path
                @test isfile(path)
                back = read_influence_diagram(path)
                @test back ≈ m
                @test optimize(back).expected_utility ≈ optimize(m).expected_utility
            end
        end
        # a plain Bayesian network reads as a diagram without decisions
        bn = read_influence_diagram(fixture_path("dne/habitat_reference.dne"))
        @test nparts(syntax(bn), :Decision) == 0
        @test has_semantics(bn)
    end
end
