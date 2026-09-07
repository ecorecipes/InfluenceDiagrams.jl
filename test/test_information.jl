@testset "Value of information (SPEC sections 35 and 55.7)" begin
    m = umbrella_model()
    noinfo = without_information(m, :Umbrella, :Forecast)

    @testset "umbrella: EVI = 7, EVPI = 21" begin
        @test expected_value_of_information(noinfo, :Forecast, :Umbrella) ≈ 7.0
        @test expected_value_of_information(noinfo, :Forecast, :Umbrella;
                                            backend=ExhaustivePolicySearch()) ≈ 7.0
        @test expected_value_of_information(noinfo, :Weather, :Umbrella) ≈ 21.0
        @test expected_value_of_perfect_information(noinfo, :Umbrella) ≈ 21.0
        @test expected_value_of_perfect_information(noinfo, :Umbrella;
                                                    backend=ExhaustivePolicySearch()) ≈ 21.0
        # relative to the forecast-informed diagram
        @test expected_value_of_perfect_information(m, :Umbrella) ≈ 14.0
        @test expected_value_of_information(m, :Weather, :Umbrella) ≈ 14.0
        # already observed: nothing to gain
        @test expected_value_of_information(m, :Forecast, :Umbrella) == 0.0
        @test expected_value_of_perfect_information(with_information(m, :Umbrella,
                                                                     :Weather),
                                                    :Umbrella) == 0.0
        # information about a variable downstream of the action is inadmissible
        @test_throws InvalidInformationSetError expected_value_of_information(two_stage_model(),
                                                                              :Result,
                                                                              :Test)
    end

    @testset "grazing: value of observing CurrentVegetation (SPEC section 46, analyses 3 and 4)" begin
        g = reference_grazing_model()
        without = without_information(g, :GrazingManagement, :CurrentVegetation)
        @test information_names(syntax(without), :GrazingManagement) == [:ClimateForecast]
        meu_with = optimize(g).expected_utility
        meu_without = optimize(without).expected_utility
        @test meu_with >= meu_without - 1e-9
        evi = expected_value_of_information(without, :CurrentVegetation, :GrazingManagement)
        @test evi ≈ meu_with - meu_without
        @test evi >= -1e-9
        @test isapprox(expected_value_of_information(without, :CurrentVegetation,
                                                     :GrazingManagement;
                                                     backend=ExhaustivePolicySearch()), evi;
                       atol=1e-9)
        evpi = expected_value_of_perfect_information(g, :GrazingManagement)
        @test evpi >= -1e-9
        @test evpi >= expected_value_of_information(g, :Climate, :GrazingManagement) - 1e-9
    end

    @testset "two-stage: EVI and EVPI with both backends (SPEC section 35)" begin
        t = two_stage_model()
        @test optimize(t).expected_utility ≈ 21.0
        # info(Oil, Test) propagates to Drill, so the enlarged diagram still has
        # no-forgetting and the default backend solves it (it threw before the fix)
        enlarged = with_information(t, :Test, :Oil)
        @test information_names(syntax(enlarged), :Test) == [:Oil]
        @test information_names(syntax(enlarged), :Drill) == [:Test, :Result, :Oil]
        @test is_no_forgetting(enlarged)
        @test optimize(enlarged).expected_utility ≈ 50.0
        @test optimize(enlarged, ExhaustivePolicySearch()).expected_utility ≈ 50.0
        for backend in (DecisionVariableElimination(), ExhaustivePolicySearch())
            @test expected_value_of_information(t, :Oil, :Test; backend=backend) ≈ 29.0
            @test expected_value_of_perfect_information(t, :Test; backend=backend) ≈ 29.0
            # observing the oil state at the later decision alone is worth the same:
            # the test is then pointless and the optimum is again 50
            @test expected_value_of_information(t, :Oil, :Drill; backend=backend) ≈ 29.0
            @test expected_value_of_information(t, :Result, :Drill; backend=backend) == 0.0
        end

        # opting out of the propagation gives a limited-memory diagram: the single-arc
        # semantics, worth 24 because the test result has to carry the signal
        single = with_information(t, :Test, :Oil; no_forgetting=false)
        @test information_names(syntax(single), :Drill) == [:Test, :Result]
        @test !is_no_forgetting(single)
        @test_throws IrregularDiagramError optimize(single)
        @test optimize(single, ExhaustivePolicySearch()).expected_utility ≈ 45.0
        @test optimize(with_no_forgetting(single)).expected_utility ≈ 50.0
    end

    @testset "EVI agrees with the oracle on seeded random two-decision diagrams" begin
        rng = MersenneTwister(4126)
        checked = 0
        for _ in 1:30
            m = random_influence_model(rng; ndecision=2)
            id = syntax(m)
            d = first(decision_order(id))
            candidates = admissible_information(id, d)
            isempty(candidates) && continue
            x = rand(rng, candidates)
            # keep the oracle affordable: the enlarged diagram has more policies
            enlarged = with_information(m, d, x)
            prod(BigInt[n_deterministic_policies(enlarged, e)
                        for e in decisions(syntax(enlarged))]; init=BigInt(1)) <= 100_000 ||
                continue
            evi = expected_value_of_information(m, x, d)
            @test evi >= -1e-9
            @test isapprox(evi,
                           expected_value_of_information(m, x, d;
                                                         backend=ExhaustivePolicySearch());
                           atol=1e-9)
            @test is_no_forgetting(enlarged)
            @test isapprox(optimize(enlarged).expected_utility,
                           optimize(enlarged, ExhaustivePolicySearch()).expected_utility;
                           atol=1e-9)
            checked += 1
            checked >= 6 && break
        end
        @test checked >= 4
    end

    @testset "information monotonicity on random diagrams" begin
        rng = MersenneTwister(77)
        checked = 0
        for _ in 1:40
            m = random_influence_model(rng; ndecision=1)
            id = syntax(m)
            d = only(decisions(id))
            candidates = admissible_information(id, d)
            isempty(candidates) && continue
            x = rand(rng, candidates)
            before = optimize(m).expected_utility
            after = optimize(with_information(m, d, x)).expected_utility
            @test after >= before - 1e-9
            @test expected_value_of_information(m, x, d) >= -1e-9
            @test optimize(m, ExhaustivePolicySearch()).expected_utility ≈ before
            @test optimize(with_information(m, d, x),
                           ExhaustivePolicySearch()).expected_utility ≈
                  after
            checked += 1
            checked >= 12 && break
        end
        @test checked >= 5
        # the policy class grows: every policy of the smaller class has an equivalent in
        # the larger class (the Lean theorem exists_strategy_enlarged_eq)
        um = umbrella_model()
        p = deterministic_policy(noinfo, :Umbrella, () -> :leave)
        @test expected_utility(noinfo, Strategy(:Umbrella => p)) ≈
              expected_utility(um,
                               Strategy(:Umbrella => deterministic_policy(um, :Umbrella,
                                                                          f -> :leave)))
    end
end
