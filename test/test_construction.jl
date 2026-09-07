@testset "Construction and inspection" begin
    id = umbrella_diagram()
    @test nparts(id, :Variable) == 3
    @test nparts(id, :Mechanism) == 2        # Weather (prior) and Forecast
    @test nparts(id, :Decision) == 1
    @test nparts(id, :InformationInput) == 1
    @test nparts(id, :Utility) == 1
    @test nparts(id, :UtilityInput) == 2
    @test nparts(id, :DecisionPrecedence) == 0

    @testset "decisions" begin
        @test decisions(id) == [1]
        @test decision_names(id) == [:Umbrella]
        @test decision_name(id, 1) == :Umbrella
        @test decision_id(id, :Umbrella) == 1
        @test decision_variable(id, :Umbrella) == variable_id(id, :Umbrella)
        @test decision_of(id, :Umbrella) == 1
        @test decision_of(id, :Weather) === nothing
        @test is_decision(id, :Umbrella)
        @test !is_decision(id, :Forecast)
        @test decision_information(id, :Umbrella) == [variable_id(id, :Forecast)]
        @test information_names(id, :Umbrella) == [:Forecast]
        @test action_variables(id) == [variable_id(id, :Umbrella)]
        @test action_names(id) == [:Umbrella]
        @test Set(chance_names(id)) == Set([:Weather, :Forecast])
        @test !has_mechanism(id, :Umbrella)
        @test parents(id, :Umbrella) == Int[]   # information arcs are not causal arcs
        @test_throws UnknownDecisionError decision_id(id, :Nope)
    end

    @testset "utilities" begin
        @test utilities(id) == [1]
        @test utility_names(id) == [:U]
        @test utility_name(id, :U) == :U
        @test utility_id(id, :U) == 1
        @test utility_ref(id, :U) == NoRef()
        @test utility_scope_names(id, :U) == [:Weather, :Umbrella]
        @test utility_scope(id, 1) ==
              [variable_id(id, :Weather), variable_id(id, :Umbrella)]
        @test_throws UnknownUtilityError utility_id(id, :V)
    end

    @testset "decision names can differ from variable names" begin
        d = influence_diagram(:X => [:a, :b], :A => [:go, :stop];
                              mechanisms=[:X => Symbol[]], closed=false)
        add_decision!(d, :A; information=[:X], name=:Choose)
        @test decision_names(d) == [:Choose]
        @test decision_id(d, :Choose) == 1
        @test decision_id(d, :A) == 1          # by action variable
        @test information_names(d, :A) == [:X]
        add_utility!(d, :V; scope=[:A])
        add_utility_input!(d, :V, :X)
        @test utility_scope_names(d, :V) == [:A, :X]
        @test subpart(d, :utility_position) == [1, 2]
        add_information!(d, :Choose, :X)      # a duplicate, reported by validate
        @test nparts(d, :InformationInput) == 2
        @test_throws InvalidInformationSetError validate(d)
    end

    @testset "precedence and decision order" begin
        t = two_stage_diagram()
        @test decision_names(t) == [:Test, :Drill]
        @test decision_order(t) == [decision_id(t, :Test), decision_id(t, :Drill)]
        @test precedences(t) == Pair{Int,Int}[]
        # Two unordered decisions: explicit precedence decides.
        u = influence_diagram(:A => [:a1, :a2], :B => [:b1, :b2], :X => [:x1, :x2];
                              mechanisms=[:X => (:A, :B)],
                              decisions=[:A => Symbol[], :B => Symbol[]],
                              utilities=[:U => :X], precedence=[:B => :A])
        @test precedences(u) == [decision_id(u, :B) => decision_id(u, :A)]
        @test decision_order(u) == [decision_id(u, :B), decision_id(u, :A)]
        @test validate(u) === nothing
        add_precedence!(u, :A => :B)
        @test_throws DecisionPrecedenceCycleError decision_order(u)
        @test_throws DecisionPrecedenceCycleError validate(u)
    end

    @testset "information graph" begin
        g = information_graph(id)
        # causal Weather -> Forecast, information Forecast -> Umbrella
        @test nv(g) == 3
        @test ne(g) == 2
        vg = variable_graph(id)
        @test ne(vg) == 1
    end

    @testset "closed keyword" begin
        open_id = influence_diagram(:X => [:a, :b], :D => [:d1, :d2];
                                    decisions=[:D => :X], closed=false)
        @test !has_mechanism(open_id, :X)
        @test_throws MissingMechanismError validate(open_id; closed=true)
        @test validate(open_id) === nothing
    end

    @testset "show" begin
        @test occursin("InfluenceDiagramModel", sprint(show, umbrella_model()))
        @test occursin("Umbrella",
                       sprint(show, Strategy(:Umbrella => ConstantPolicy(:take))))
    end
end
