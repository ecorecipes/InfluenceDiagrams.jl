@testset "Instantiate (Proposition 5)" begin
    @testset "umbrella" begin
        m = umbrella_model()
        σ = Strategy(:Umbrella => deterministic_policy(m, :Umbrella,
                                                       f -> f == :rainy ? :take : :leave))
        bn = instantiate(m, σ)
        @test bn isa BayesModel
        @test syntax(bn) isa BayesNet
        @test validate(bn; closed=true, unique_names=true, semantics=true) === nothing
        @test nparts(syntax(bn), :Mechanism) == 3
        mech = mechanism_of(syntax(bn), :Umbrella)
        @test mechanism_name(syntax(bn), mech) == policy_mechanism_name(:Umbrella)
        @test kernel_ref(syntax(bn), mech) == PolicyRef(:Umbrella)
        @test variable_name.(Ref(syntax(bn)), inputs(syntax(bn), mech)) == [:Forecast]
        @test kernel(bn, :Umbrella) == policy_kernel(σ[:Umbrella])
        J = joint_distribution(bn)
        @test sum(J.table) ≈ 1
        @test extras(bn)[:decisions] == [:Umbrella]
        @test extras(bn)[:source] == :influence_diagram
        @test haskey(extras(bn)[:utilities], :U)
        # evidence and history are carried over
        bn2 = instantiate(observe(m, :Forecast => :rainy), σ)
        @test evidence(bn2) == Dict(:Forecast => :rainy)
        bn3 = instantiate(do_intervention(m, :Weather => :rainy), σ)
        @test length(history(bn3)) == 1
        # constant policies reach every information state
        bn4 = instantiate(fix_decision(m, :Umbrella => :take))
        @test marginal(bn4, :Umbrella).table ≈ [1.0, 0.0]
        # the original model is untouched
        @test nparts(syntax(m), :Mechanism) == 2
    end

    @testset "grazing and two-stage" begin
        g = reference_grazing_model()
        bn = instantiate(fix_decision(g, :GrazingManagement => :reduce))
        @test validate(bn; closed=true, unique_names=true, semantics=true) === nothing
        @test sum(joint_distribution(bn).table) ≈ 1
        mech = mechanism_of(syntax(bn), :GrazingManagement)
        @test variable_name.(Ref(syntax(bn)), inputs(syntax(bn), mech)) ==
              [:ClimateForecast, :CurrentVegetation]
        t = two_stage_model()
        σ = Strategy(:Test => ConstantPolicy(:test),
                     :Drill => deterministic_policy(t, :Drill,
                                                    (test, r) -> r == :pos ? :drill : :dont))
        bn = instantiate(t, σ)
        @test validate(bn; closed=true, unique_names=true, semantics=true) === nothing
        @test sum(joint_distribution(bn).table) ≈ 1
        @test (o -> findfirst(==(:Test), o) < findfirst(==(:Drill), o))(collect(variable_name.(Ref(syntax(bn)),
                                                                                               topological_order(syntax(bn)))))
    end

    @testset "stochastic policies" begin
        m = umbrella_model()
        k = cpt([FiniteAxis(:Forecast, [:sunny, :cloudy, :rainy])],
                FiniteAxis(:Umbrella, [:take, :leave]), [0.1 0.9; 0.5 0.5; 0.9 0.1])
        bn = instantiate(m, Strategy(:Umbrella => StochasticPolicy(k)))
        @test validate(bn; closed=true, semantics=true) === nothing
        @test sum(joint_distribution(bn).table) ≈ 1
        @test kernel(bn, :Umbrella) == k
    end

    @testset "errors" begin
        m = umbrella_model()
        @test_throws IncompleteStrategyError instantiate(m, Strategy())
        @test_throws PolicySignatureError instantiate(m,
                                                      Strategy(:Umbrella => ConstantPolicy(:fly)))
        bad = DeterministicPolicy(:Umbrella, FiniteAxis[],
                                  FiniteAxis(:Umbrella, [:take, :leave]),
                                  :take)
        @test_throws PolicySignatureError instantiate(m, Strategy(:Umbrella => bad))
        # an invalid diagram cannot be instantiated
        id = umbrella_diagram()
        add_information!(id, :Umbrella, :Umbrella)
        @test_throws InvalidInformationSetError instantiate(InfluenceDiagramModel(id),
                                                            Strategy(:Umbrella => ConstantPolicy(:take)))
    end

    @testset "random diagrams (SPEC section 56 item 5)" begin
        rng = MersenneTwister(5)
        for _ in 1:20
            m = random_influence_model(rng)
            id = syntax(m)
            σ = Strategy(Dict{Symbol,AbstractPolicy}(decision_name(id, d) => first(all_deterministic_policies(m,
                                                                                                              d))
                                                     for d in decisions(id)))
            bn = instantiate(m, σ)
            @test validate(bn; closed=true, unique_names=true, semantics=true) === nothing
            @test sum(joint_distribution(bn).table) ≈ 1
            @test nparts(syntax(bn), :Mechanism) == nparts(id, :Variable)
        end
    end
end
