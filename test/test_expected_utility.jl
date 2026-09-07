@testset "Expected utility (Proposition 6)" begin
    m = umbrella_model()

    # Independent brute force: enumerate weather, forecast and the policy's action.
    function umbrella_brute(policy)
        PW = Dict(:sunny => 0.7, :rainy => 0.3)
        PF = Dict(:sunny => Dict(:sunny => 0.7, :cloudy => 0.2, :rainy => 0.1),
                  :rainy => Dict(:sunny => 0.15, :cloudy => 0.25, :rainy => 0.6))
        U = Dict((:sunny, :take) => 20.0, (:sunny, :leave) => 100.0,
                 (:rainy, :take) => 70.0,
                 (:rainy, :leave) => 0.0)
        eu = 0.0
        for w in (:sunny, :rainy), f in (:sunny, :cloudy, :rainy)
            eu += PW[w] * PF[w][f] * U[(w, policy(f))]
        end
        return eu
    end

    @testset "umbrella numbers" begin
        @test expected_utility(m, :Umbrella => :leave) ≈ 70.0
        @test expected_utility(m, :Umbrella => :take) ≈ 35.0
        @test expected_utility(fix_decision(m, :Umbrella => :leave)) ≈ 70.0
        @test expected_utility(m, Strategy(:Umbrella => ConstantPolicy(:leave))) ≈ 70.0
        @test expected_utility(m, [:Umbrella => :leave]) ≈ 70.0
        best = deterministic_policy(m, :Umbrella, f -> f == :rainy ? :take : :leave)
        @test expected_utility(m, Strategy(:Umbrella => best)) ≈ 77.0
        @test umbrella_brute(f -> f == :rainy ? :take : :leave) ≈ 77.0
        for p in all_deterministic_policies(m, :Umbrella)
            @test expected_utility(m, Strategy(:Umbrella => p)) ≈ umbrella_brute(p)
        end
        # perfect information: observe the weather instead of the forecast
        perfect = with_information(without_information(m, :Umbrella, :Forecast), :Umbrella,
                                   :Weather)
        pw = deterministic_policy(perfect, :Umbrella, w -> w == :rainy ? :take : :leave)
        @test expected_utility(perfect, Strategy(:Umbrella => pw)) ≈ 91.0
    end

    @testset "total_utility on instantiated networks" begin
        bn = instantiate(m, Strategy(:Umbrella => ConstantPolicy(:take)))
        @test total_utility(bn,
                            Dict(:Weather => :rainy, :Umbrella => :take,
                                 :Forecast => :sunny)) ==
              70.0
        @test expected_utility(bn) ≈ 35.0
        @test_throws ArgumentError expected_utility(BayesianNetworks.reference_habitat_model())
    end

    @testset "evidence conditions the expectation" begin
        e = observe(m, :Forecast => :rainy)
        # P(rainy | F = rainy) = 0.18 / 0.25 = 0.72
        @test expected_utility(e, :Umbrella => :take) ≈ 0.28 * 20 + 0.72 * 70
        @test expected_utility(e, :Umbrella => :leave) ≈ 0.28 * 100
        @test_throws ImpossibleEvidenceError expected_utility(observe(do_intervention(m,
                                                                                      :Weather =>
                                                                                          :rainy),
                                                                      :Weather => :sunny),
                                                              :Umbrella => :take)
    end

    @testset "linearity and additive aggregation" begin
        g = reference_grazing_model()
        fixed = fix_decision(g, :GrazingManagement => :reduce)
        eu = expected_utility(fixed)
        # the cost of `reduce` is -15; the rest is the expected conservation benefit
        gb = InfluenceDiagramModel(syntax(g); kernels=kernels(g),
                                   utilities=Dict{Symbol,AbstractUtility}(:ConservationBenefit =>
                                                                              utility(g,
                                                                                      :ConservationBenefit),
                                                                          :ManagementCost =>
                                                                              TabularUtility(utility(g,
                                                                                                     :ManagementCost).scope,
                                                                                             zeros(3))),
                                   strategy=strategy(fixed))
        @test expected_utility(gb) ≈ eu + 15
        @test expected_utility(gb) ≈
              100 * marginal(instantiate(fixed), :Biodiversity).table[2]
        # SPEC section 46 analysis 1: expected utility of each fixed action
        eus = Dict(a => expected_utility(g, :GrazingManagement => a)
                   for a in (:exclude, :reduce, :maintain))
        @test all(isfinite, values(eus))
        @test eus[:exclude] < eus[:reduce]   # excluding grazing costs 40
    end

    @testset "two-stage" begin
        t = two_stage_model()
        drill_on_pos = deterministic_policy(t, :Drill,
                                            (test, r) -> r == :pos ? :drill : :dont)
        @test expected_utility(t,
                               Strategy(:Test => ConstantPolicy(:test),
                                        :Drill => drill_on_pos)) ≈ 21.0
        always = deterministic_policy(t, :Drill, (test, r) -> :drill)
        @test expected_utility(t,
                               Strategy(:Test => ConstantPolicy(:skip), :Drill => always)) ≈
              20.0
        never = deterministic_policy(t, :Drill, (test, r) -> :dont)
        @test expected_utility(t,
                               Strategy(:Test => ConstantPolicy(:skip), :Drill => never)) ≈
              0.0
    end

    @testset "random models: exhaustive brute force equals the value table" begin
        rng = MersenneTwister(11)
        for _ in 1:6
            m = random_influence_model(rng; ndecision=1)
            fast = optimize(m, ExhaustivePolicySearch())
            slow = optimize(m, ExhaustivePolicySearch(; brute_force=true))
            @test fast.expected_utility ≈ slow.expected_utility
            @test expected_utility(m, fast.strategy) ≈ fast.expected_utility
            @test fast.diagnostics.method == :value_table
            @test slow.diagnostics.method == :brute_force
        end
    end
end
