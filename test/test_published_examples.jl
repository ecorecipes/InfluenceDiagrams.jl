# Two limited-memory problems with published answers, on every backend that takes them.
# The targets are the numbers printed in the DecisionProgramming.jl documentation
# (github.com/gamma-opt/DecisionProgramming.jl), an implementation that shares no code
# with this package: used car buyer, mean 31.000000; pig breeding with N = 4, mean
# 726.812100 and P(ill at the sale) 0.305167.
using HiGHS: HiGHS

@testset "published limited-memory examples" begin
    backends = ["exhaustive" => ExhaustivePolicySearch(),
                "branch and bound" => BranchAndBoundPolicySearch(),
                "mixed integer" => MixedIntegerPolicySearch(HiGHS.Optimizer)]

    @testset "the used car buyer (Howard 1977)" begin
        m = used_car_buyer_model()
        @test validate(m; closed=true, semantics=true, unique_names=true) === nothing
        @test !is_no_forgetting(m)
        @test_throws IrregularDiagramError optimize(m)
        for (name, backend) in backends
            solution = optimize(m, backend)
            @test isapprox(solution.expected_utility, 31; atol=1e-9)
            σ = solution.strategy
            @test σ[:Test]() === :test
            @test σ[:Purchase](:lemon) === :with_guarantee
            @test σ[:Purchase](:peach) === :without_guarantee
        end
        # Without the test: 28, by buying without the guarantee. `optimize` ignores a
        # model's own strategy, so the comparison is over the purchase policies with the
        # test decision's policy held at `no_test`.
        untested = maximum(expected_utility(m,
                                            Strategy(:Test => ConstantPolicy(:no_test),
                                                     :Purchase => ConstantPolicy(a)))
                           for a in (:without_guarantee, :with_guarantee, :none))
        @test untested ≈ 28
        @test expected_utility(m,
                               Strategy(:Test => ConstantPolicy(:no_test),
                                        :Purchase => ConstantPolicy(:without_guarantee))) ≈
              28
    end

    @testset "pig breeding, four months (Lauritzen and Nilsson 2001)" begin
        m = pig_breeding_model()
        @test validate(m; closed=true, semantics=true, unique_names=true) === nothing
        @test !is_no_forgetting(m)
        @test n_deterministic_strategies(m) == 64
        for (name, backend) in backends
            solution = optimize(m, backend)
            @test isapprox(solution.expected_utility, 726.8121; atol=5e-5)
            σ = solution.strategy
            @test σ[:Treat1](:positive) === :pass && σ[:Treat1](:negative) === :pass
            for k in (2, 3)
                decision = Symbol(:Treat, k)
                @test σ[decision](:positive) === :treat
                @test σ[decision](:negative) === :pass
            end
        end
        # The probability that the pig is ill when sold, read from the sale alone.
        σ = optimize(m, BranchAndBoundPolicySearch()).strategy
        sale_only = bind_utility(m, [Symbol(:Cost, k) => [0.0, 0.0] for k in 1:3])
        ill = (1000 - expected_utility(sale_only, σ)) / 700
        @test isapprox(ill, 0.305167; atol=5e-7)
        # Treating always, or never, does worse.
        constant(a) = Strategy((Symbol(:Treat, k) => ConstantPolicy(a) for k in 1:3)...)
        @test expected_utility(m, constant(:treat)) < 726.8
        @test expected_utility(m, constant(:pass)) < 726.8
        @test_throws ArgumentError pig_breeding_model(; months=1)
    end

    @testset "pig breeding beyond enumeration" begin
        # 2^58 joint states and 4^19 strategies; the clusters stay at eight states.
        m = pig_breeding_model(; months=20)
        @test n_deterministic_strategies(m) == big(4)^19
        tree = rooted_junction_tree(m)
        @test maximum(length, values(tree.clusters)) == 3
        solution = optimize(m, MixedIntegerPolicySearch(HiGHS.Optimizer))
        @test !solution.diagnostics.verified
        @test solution.diagnostics.largest_cluster == 8
        @test 300 < solution.expected_utility < 1000
        # Six months is the largest the search enumerates at the default limit, and the
        # two agree there.
        six = pig_breeding_model(; months=6)
        @test isapprox(optimize(six,
                                MixedIntegerPolicySearch(HiGHS.Optimizer)).expected_utility,
                       optimize(six, BranchAndBoundPolicySearch()).expected_utility;
                       rtol=1e-9)
    end
end
