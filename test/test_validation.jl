@testset "Validation" begin
    @testset "valid diagrams" begin
        for id in (umbrella_diagram(), reference_grazing_diagram(), two_stage_diagram())
            @test validate(id) === nothing
            @test validate(id; closed=true, unique_names=true) === nothing
            @test isvalid(id; closed=true)
            @test isempty(validation_errors(id; closed=true))
        end
    end

    @testset "closed treats actions as generated" begin
        id = umbrella_diagram()
        @test !has_mechanism(id, :Umbrella)
        @test validate(id; closed=true) === nothing
        # the Bayesian-network part alone is open
        @test_throws MissingMechanismError validate(BayesNet(id); closed=true)
        # a chance variable without a mechanism is still reported
        open_id = influence_diagram(:X => [:a, :b], :D => [:d1, :d2];
                                    decisions=[:D => :X], closed=false)
        errs = validation_errors(open_id; closed=true)
        @test errs == [MissingMechanismError(:X, variable_id(open_id, :X))]
    end

    @testset "item 1: at most one decision per variable" begin
        id = umbrella_diagram()
        add_decision!(id, :Umbrella; name=:Again)
        @test_throws DecisionUniquenessError validate(id)
        e = first(validation_errors(id))
        @test e == DecisionUniquenessError(:Again, :Umbrella, :duplicate_decision)
        @test_throws DecisionUniquenessError decision_of(id, :Umbrella)
        @test occursin("Umbrella", sprint(showerror, e))
    end

    @testset "item 2: actions have no chance mechanism" begin
        id = umbrella_diagram()
        add_mechanism!(id, :Umbrella; inputs=[:Forecast])
        errs = validation_errors(id)
        @test DecisionUniquenessError(:Umbrella, :Umbrella, :has_mechanism) in errs
        @test occursin("chance mechanism",
                       sprint(showerror,
                              DecisionUniquenessError(:Umbrella, :Umbrella, :has_mechanism)))
    end

    @testset "item 3: information inputs are valid" begin
        id = umbrella_diagram()
        i = add_part!(id, :InformationInput; information_decision=1, information_position=2)
        @test_throws DanglingReferenceError validate(id)
        @test DanglingReferenceError(:InformationInput, i, :information_variable, 0) in
              validation_errors(id)
        id = umbrella_diagram()
        i = add_part!(id, :InformationInput; information_variable=1, information_position=2)
        @test DanglingReferenceError(:InformationInput, i, :information_decision, 0) in
              validation_errors(id)
        id = umbrella_diagram()
        d = add_part!(id, :Decision; decision_name=:orphan)
        @test DanglingReferenceError(:Decision, d, :decision_variable, 0) in
              validation_errors(id)
        id = umbrella_diagram()
        add_information!(id, :Umbrella, :Umbrella)
        @test InvalidInformationSetError(:Umbrella, :Umbrella, :self) in
              validation_errors(id)
        id = umbrella_diagram()
        add_information!(id, :Umbrella, :Forecast)
        @test InvalidInformationSetError(:Umbrella, :Forecast, :duplicate) in
              validation_errors(id)
        @test occursin("own action",
                       sprint(showerror, InvalidInformationSetError(:D, :D, :self)))
        @test occursin("does not exist",
                       sprint(showerror, InvalidInformationSetError(:D, :X, :unknown)))
    end

    @testset "item 4: information is available before the decision" begin
        # Wet depends causally on the umbrella; it cannot inform the umbrella decision.
        id = influence_diagram(:Weather => [:sunny, :rainy], :Umbrella => [:take, :leave],
                               :Wet => [:no, :yes];
                               mechanisms=[:Wet => (:Weather, :Umbrella)],
                               decisions=[:Umbrella => :Wet], utilities=[:U => :Wet])
        @test_throws InvalidInformationSetError validate(id)
        e = first(validation_errors(id))
        @test e == InvalidInformationSetError(:Umbrella, :Wet, :downstream)
        @test occursin("downstream", sprint(showerror, e))
        @test_throws DecisionPrecedenceCycleError decision_order(id)
        # variable_graph stays acyclic: information arcs are not causal
        @test is_acyclic(id)
    end

    @testset "item 5: utilities are never parents (by construction)" begin
        id = umbrella_diagram()
        # a utility node is not a variable, so it cannot be an input, an information
        # variable or a utility input
        @test !has_variable(id, :U)
        @test_throws UnknownVariableError add_mechanism!(id, :Weather; inputs=[:U])
    end

    @testset "item 6: utility inputs are valid" begin
        id = umbrella_diagram()
        i = add_part!(id, :UtilityInput; utility_node=1, utility_position=3)
        @test_throws DanglingReferenceError validate(id)
        @test DanglingReferenceError(:UtilityInput, i, :utility_variable, 0) in
              validation_errors(id)
        id = umbrella_diagram()
        i = add_part!(id, :UtilityInput; utility_variable=1, utility_position=3)
        @test DanglingReferenceError(:UtilityInput, i, :utility_node, 0) in
              validation_errors(id)
        id = umbrella_diagram()
        add_utility_input!(id, :U, :Weather)
        e = first(validation_errors(id))
        @test e isa UtilityScopeError
        @test e.utility == :U && e.what == :duplicate
        @test occursin("UtilityScopeError", sprint(showerror, e))
    end

    @testset "item 7: utility references resolve" begin
        m = InfluenceDiagramModel(umbrella_diagram())
        @test validate(m) === nothing
        @test_throws MissingKernelError validate(m; semantics=true)
        m = bind_cpt(m, [:Weather => [0.7, 0.3], :Forecast => [0.7 0.2 0.1; 0.15 0.25 0.6]])
        @test_throws MissingUtilityError validate(m; semantics=true)
        @test missing_utilities(m) == [:U]
        @test_throws MissingUtilityError utility(m, :U)
        m = umbrella_model()
        @test validate(m; semantics=true, closed=true) === nothing
        @test occursin("does not resolve",
                       sprint(showerror, MissingUtilityError(:U, NoRef())))
    end

    @testset "item 8: precedence is acyclic" begin
        t = two_stage_diagram()
        add_precedence!(t, :Drill => :Test)   # contradicts the information arc Test -> Drill
        @test_throws DecisionPrecedenceCycleError validate(t)
        @test_throws DecisionPrecedenceCycleError decision_order(t)
        e = first(validation_errors(t))
        @test occursin("cycle", sprint(showerror, e))
        u = influence_diagram(:A => [:a1, :a2], :B => [:b1, :b2];
                              decisions=[:A => Symbol[], :B => Symbol[]],
                              precedence=[:A => :B, :B => :A])
        @test DecisionPrecedenceCycleError([:A, :B]) in validation_errors(u)
        u = influence_diagram(:A => [:a1, :a2], :B => [:b1, :b2];
                              decisions=[:A => Symbol[], :B => Symbol[]])
        p = add_part!(u, :DecisionPrecedence; earlier=1)
        @test DanglingReferenceError(:DecisionPrecedence, p, :later, 0) in
              validation_errors(u)
    end

    @testset "items 9 and 10: policies and strategies" begin
        m = umbrella_model()
        bad = ConstantPolicy(:sideways)
        @test_throws PolicySignatureError set_policy(m, :Umbrella, bad)
        @test_throws PolicySignatureError validate_policy(m, :Umbrella, bad)
        wrong_info = DeterministicPolicy(:Umbrella, FiniteAxis[],
                                         FiniteAxis(:Umbrella, [:take, :leave]),
                                         :take)
        e = try
            validate_policy(m, :Umbrella, wrong_info)
        catch err
            err
        end
        @test e isa PolicySignatureError && e.what == :information
        @test occursin("information", sprint(showerror, e))
        @test_throws IncompleteStrategyError validate(m; strategy=true)
        @test_throws IncompleteStrategyError instantiate(m)
        @test_throws IncompleteStrategyError expected_utility(m)
        @test occursin("Umbrella", sprint(showerror, IncompleteStrategyError([:Umbrella])))
        m2 = fix_decision(m, :Umbrella => :take)
        @test validate(m2; strategy=true, semantics=true, closed=true) === nothing
        # a policy for a decision that does not exist
        m3 = InfluenceDiagramModel(m.model; utilities=bound_utilities(m),
                                   strategy=Strategy(:Nope => ConstantPolicy(:take)))
        @test_throws UnknownDecisionError validate(m3)
    end

    @testset "item 11: causal acyclicity with actions exogenous" begin
        id = influence_diagram(:X => [:a, :b], :Y => [:c, :d], :D => [:d1, :d2];
                               mechanisms=[:X => :Y, :Y => (:X, :D)],
                               decisions=[:D => Symbol[]])
        @test_throws CyclicBayesNetError validate(id)
        @test_throws CyclicBayesNetError decision_order(id)
    end

    @testset "item 12: information wiring is never causal" begin
        id = umbrella_diagram()
        @test nparts(id, :Input) == 1    # only Weather -> Forecast
        @test parents(id, :Umbrella) == Int[]
        @test children(id, :Forecast) == Int[]
        m = umbrella_model()
        bn = instantiate(m, Strategy(:Umbrella => ConstantPolicy(:take)))
        # the policy mechanism reads the information set, and nothing else does
        @test variable_name.(Ref(syntax(bn)), parents(syntax(bn), :Umbrella)) == [:Forecast]
    end

    @testset "positions" begin
        id = umbrella_diagram()
        set_subpart!(id, 1, :information_position, 3)
        e = first(validation_errors(id))
        @test e isa PositionError && e.part == :InformationInput
        id = umbrella_diagram()
        set_subpart!(id, 1, :utility_position, 2)
        e = first(validation_errors(id))
        @test e isa PositionError && e.part == :UtilityInput
    end

    @testset "unique names" begin
        id = umbrella_diagram()
        add_utility!(id, :U; scope=[:Weather])
        @test validate(id) === nothing
        @test_throws DuplicateNameError validate(id; unique_names=true)
        @test_throws DuplicateNameError utility_id(id, :U)
    end

    @testset "error messages" begin
        for e in (UnknownDecisionError(:D), UnknownUtilityError(:U),
                  DecisionPrecedenceCycleError([:A, :B]),
                  PolicySignatureError(:D, :action, 1, 2),
                  UtilityScopeError(:U, :table, (2,), (3,)), IncompleteStrategyError([:D]),
                  PolicySearchTooLargeError(10, 5), UnsupportedAggregationError(:M, [0.5]),
                  IrregularDiagramError(:D, [:X], :information),
                  IrregularDiagramError(:D, [:X], :probability),
                  EvidenceOnActionError(:X, :D, :x),
                  UneliminatedVariablesError([:X, :Y]))
            @test e isa InfluenceDiagramError
            @test e isa BayesNetError
            @test occursin(string(nameof(typeof(e))), sprint(showerror, e))
        end
    end
end
