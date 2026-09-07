@testset "Graphviz drawings" begin
    using BayesianNetworks: Graphviz

    _nodes(g) = [s for s in g.stmts if s isa Graphviz.Node]
    _edges(g) = [s for s in g.stmts if s isa Graphviz.Edge]

    @testset "umbrella: one node per variable and utility, dashed information arcs" begin
        id = umbrella_diagram()
        g = to_graphviz(id)
        @test g isa Graphviz.Graph
        @test g.directed
        @test length(_nodes(g)) == nparts(id, :Variable) + nparts(id, :Utility)
        # Forecast <- Weather, Forecast --> Umbrella (information), (Weather, Umbrella) -> U
        @test length(_edges(g)) == 1 + 1 + 2
        dashed = [e for e in _edges(g) if get(e.attrs, :style, "") == "dashed"]
        @test length(dashed) == nparts(id, :InformationInput) == 1
        shapes = sort!([n.attrs[:shape] for n in _nodes(g)])
        @test shapes == ["box", "diamond", "ellipse", "ellipse"]
        # states are labelled by default and suppressed on request
        @test any(n -> occursin("sunny", n.attrs[:label]), _nodes(g))
        @test !any(n -> occursin("sunny", n.attrs[:label]),
                   _nodes(to_graphviz(id; states=false)))
        @test occursin("rankdir", sprint(show, to_graphviz(id; rankdir="LR")))
    end

    @testset "models carry evidence and interventions" begin
        m = observe(umbrella_model(), :Forecast => :rainy)
        g = to_graphviz(m)
        shaded = [n for n in _nodes(g) if get(n.attrs, :fillcolor, "") == "lightgrey"]
        @test length(shaded) == 1
        @test occursin("Forecast = rainy", only(shaded).attrs[:label])
        d = to_graphviz(do_intervention(umbrella_model(), :Weather => :rainy))
        doubled = [n for n in _nodes(d) if get(n.attrs, :peripheries, "") == "2"]
        @test length(doubled) == 1
        @test occursin("do(Weather = rainy)", only(doubled).attrs[:label])
        # explicit keyword overrides and attribute merging
        g2 = to_graphviz(umbrella_diagram(); intervened=[:Weather],
                         graph_attrs=Dict(:bgcolor => "white"),
                         node_attrs=Dict(:fontsize => "9"),
                         edge_attrs=Dict(:color => "grey"), name="Umbrella")
        @test g2.name == "Umbrella"
        @test g2.graph_attrs[:bgcolor] == "white"
        @test g2.node_attrs[:fontsize] == "9"
        @test g2.edge_attrs[:color] == "grey"
        @test any(n -> get(n.attrs, :peripheries, "") == "2", _nodes(g2))
    end

    @testset "grazing and two-stage draw" begin
        for id in (reference_grazing_diagram(), two_stage_diagram())
            g = to_graphviz(id)
            @test length(_nodes(g)) == nparts(id, :Variable) + nparts(id, :Utility)
            @test length([e for e in _edges(g) if get(e.attrs, :style, "") == "dashed"]) ==
                  nparts(id, :InformationInput)
            @test !isempty(sprint(show, g))
        end
    end
end
