@testset "Exact-arithmetic stable DVE" begin
    diagram = influence_diagram(:H => [:low, :high], :D => [:leave, :act];
                                decisions=[:D => ()],
                                utilities=[:Swing => :H, :Offset => :H])
    model = bind_cpt(InfluenceDiagramModel(diagram), :H => [.5, .5])
    model = bind_utility(model, [:Swing => [1e16, -1e16], :Offset => [1.0, 1.0]])
    @test optimize(model).expected_utility == 0.0
    stable = optimize(model, DecisionVariableElimination(stable=true))
    @test stable.expected_utility == 1.0
    @test stable.diagnostics.arithmetic == :exact_rational
    @test stable.diagnostics.exact_probability_guards
    @test DecisionVariableElimination(BayesianNetworkInference.MinFill(), 1e-9).stable == false

    private = influence_diagram(:H => [:low, :high], :D => [:leave, :act];
                                decisions=[:D => :H],
                                utilities=[:Background => (:H, :D), :Gain => :D])
    private = bind_cpt(InfluenceDiagramModel(private), :H => [.5, .5])
    private = bind_utility(private, [:Background => [1e300 1e300; -1e300 -1e300],
                                    :Gain => [-1e-300, 1e-300]])
    result = optimize(private, DecisionVariableElimination(stable=true))
    @test result.expected_utility == 1e-300
    @test all(==(:act), policy_table(result.strategy[:D]))

    rare = influence_diagram(:A => [:rare, :usual], :B => [:rare, :usual], :D => [:leave, :act];
                             decisions=[:D => ()], utilities=[:Value => :D])
    rare = bind_cpt(InfluenceDiagramModel(rare), [:A => [1e-200, 1.0], :B => [1e-200, 1.0]])
    rare = observe(bind_utility(rare, :Value => [-2.0, 3.0]), [:A => :rare, :B => :rare])
    result = optimize(rare, DecisionVariableElimination(stable=true))
    @test result.expected_utility == 3.0
    @test result.diagnostics.mass_status == :underflow
    @test result.diagnostics.log_evidence_probability ≈ 2log(1e-200)
    @test result.diagnostics.evidence_probability == 0.0
    @test_throws BayesianNetworks.ImpossibleEvidenceError optimize(
        bind_cpt(rare, :A => [0.0, 1.0]), DecisionVariableElimination(stable=true))

    names = [Symbol("D", i) for i in 1:6]
    large = influence_diagram((name => [:leave, :act] for name in names)...;
                               decisions=[name => names[1:(i-1)] for (i, name) in enumerate(names)],
                               utilities=[Symbol("U", i) => name for (i, name) in enumerate(names)])
    large = bind_utility(InfluenceDiagramModel(large), [Symbol("U", i) => [0.0, 1.0] for i in 1:6])
    @test_throws PolicySearchTooLargeError optimize(large, ExhaustivePolicySearch())
    result = optimize(large, DecisionVariableElimination(stable=true))
    @test result.expected_utility == 6.0
    @test result.diagnostics.max_factor_size == 2
    @test all(all(==(:act), policy_table(result.strategy[name])) for name in names)

    rng = MersenneTwister(20260910)
    for _ in 1:12
        m = random_influence_model(rng; nchance=3, ndecision=2, max_info_states=4)
        result = optimize(m, DecisionVariableElimination(stable=true))
        reference = optimize(m, ExhaustivePolicySearch(stable=true))
        @test result.expected_utility ≈ reference.expected_utility atol=1e-12
        @test expected_utility(m, result.strategy; stable=true) ≈ result.expected_utility atol=1e-12
    end
    forgetting = without_information(two_stage_model(), :Drill, :Test)
    @test_throws IrregularDiagramError optimize(forgetting, DecisionVariableElimination(stable=true))

    midpoint = (Rational{BigInt}(1.0) + Rational{BigInt}(nextfloat(1.0))) / 2
    cases = [big(0)//1, big(1)//3, -big(1)//3, big(1)//big(2)^1074,
             big(1)//big(2)^1075, -big(1)//big(2)^1075,
             midpoint, midpoint - big(1)//big(2)^500, midpoint + big(1)//big(2)^500]
    for precision in (16, 53, 256)
        setprecision(precision) do
            for value in cases
                rounded = InfluenceDiagrams._nearest_binary64(value)
                @test InfluenceDiagrams._dve_rounds_to(value, rounded)
            end
            @test InfluenceDiagrams._nearest_binary64(midpoint) == 1.0
            @test InfluenceDiagrams._nearest_binary64(midpoint + big(1)//big(2)^500) == nextfloat(1.0)
            result = optimize(rare, DecisionVariableElimination(stable=true))
            @test result.expected_utility == 3.0
            @test result.diagnostics.log_evidence_probability ≈ 2log(1e-200)
        end
    end
    boundary = Rational{BigInt}(floatmax(Float64)) + big(2)^970
    @test InfluenceDiagrams._nearest_binary64(boundary) == Inf
    @test InfluenceDiagrams._nearest_binary64(boundary - 1) == floatmax(Float64)
end

@testset "Integer binary64 word construction" begin
    rounded_word = value -> reinterpret(UInt64, InfluenceDiagrams._nearest_binary64(value))
    lower_words = UInt64[0x0000000000000000, 0x0000000000000001, 0x000ffffffffffffe,
                         0x000fffffffffffff, 0x0010000000000000, 0x0010000000000001,
                         0x3fefffffffffffff, 0x3ff0000000000000, 0x3ff0000000000001,
                         0x7feffffffffffffe]
    for word in lower_words
        upper_word = word + UInt64(1)
        lower = Rational{BigInt}(reinterpret(Float64, word))
        upper = Rational{BigInt}(reinterpret(Float64, upper_word))
        midpoint = (lower + upper) / 2
        delta = (upper - lower) / big(2)^30
        even_word = iseven(word) ? word : upper_word
        @test rounded_word(midpoint) == even_word
        @test rounded_word(midpoint - delta) == word
        @test rounded_word(midpoint + delta) == upper_word
        @test rounded_word(-midpoint) == (even_word | 0x8000000000000000)
        @test rounded_word(-(midpoint - delta)) == (word | 0x8000000000000000)
        @test rounded_word(-(midpoint + delta)) == (upper_word | 0x8000000000000000)
    end
    threshold = Rational{BigInt}(floatmax(Float64)) + big(2)^970
    @test rounded_word(threshold) == 0x7ff0000000000000
    @test rounded_word(-threshold) == 0xfff0000000000000
    @test rounded_word(threshold - 1) == 0x7fefffffffffffff
    @test rounded_word(-(threshold - 1)) == 0xffefffffffffffff
    @test rounded_word(big(1)//big(2)^2000) == 0x0000000000000000
    @test rounded_word(-big(1)//big(2)^2000) == 0x8000000000000000
    rng = MersenneTwister(20260911)
    for _ in 1:200
        word = rand(rng, UInt64)
        exponent = (word >> 52) & 0x7ff
        exponent == 0x7ff && continue
        value = reinterpret(Float64, word)
        expected = iszero(value) ? UInt64(0) : word
        @test rounded_word(Rational{BigInt}(value)) == expected
    end
end
