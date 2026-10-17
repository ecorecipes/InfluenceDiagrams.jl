@testset "Policies and strategies" begin
    F = FiniteAxis(:Forecast, [:sunny, :cloudy, :rainy])
    A = FiniteAxis(:Umbrella, [:take, :leave])

    @testset "DeterministicPolicy" begin
        p = DeterministicPolicy(:Umbrella, [F], A, [:leave, :leave, :take])
        @test p isa AbstractPolicy
        @test policy_table(p) == [:leave, :leave, :take]
        @test p(:rainy) == :take
        @test p(:sunny) == :leave
        @test p(Dict(:Forecast => :cloudy, :Weather => :sunny)) == :leave
        k = policy_kernel(p)
        @test k isa FiniteKernel
        @test k.dom == FiniteSpace(F) && k.codom == FiniteSpace(A)
        @test probability(k, :take, :rainy) == 1.0
        @test probability(k, :leave, :rainy) == 0.0
        @test policy_kernel(p, FiniteSpace(F), FiniteSpace(A)) == k
        @test_throws PolicySignatureError policy_kernel(p, FiniteSpace(), FiniteSpace(A))
        # dictionary and function forms
        pd = DeterministicPolicy(:Umbrella, [F], A,
                                 Dict((:sunny,) => :leave, (:cloudy,) => :leave,
                                      (:rainy,) => :take))
        pf = DeterministicPolicy(:Umbrella, [F], A, f -> f == :rainy ? :take : :leave)
        @test pd == p && pf == p
        @test hash(pd) == hash(p)
        @test_throws PolicySignatureError DeterministicPolicy(:Umbrella, [F], A,
                                                              Dict((:sunny,) => :leave))
        # bad tables
        @test_throws PolicySignatureError DeterministicPolicy(:Umbrella, [F], A,
                                                              [:take, :take])
        @test_throws PolicySignatureError DeterministicPolicy(:Umbrella, [F], A,
                                                              [:take, :take, :fly])
        @test_throws PolicySignatureError p(:sunny, :sunny)
        # no information: a single label
        p0 = DeterministicPolicy(:Umbrella, FiniteAxis[], A, :take)
        @test p0() == :take
        @test size(policy_table(p0)) == ()
        @test policy_kernel(p0).dom == FiniteSpace()
    end

    @testset "StochasticPolicy" begin
        k = cpt([F], A, [0.9 0.1; 0.5 0.5; 0.1 0.9])
        s = StochasticPolicy(:Umbrella, k)
        @test policy_kernel(s) === k
        @test StochasticPolicy(k) == s
        @test policy_kernel(s, FiniteSpace(F), FiniteSpace(A)) == k
        @test_throws PolicySignatureError policy_kernel(s, FiniteSpace(F), FiniteSpace(F))
        @test_throws PolicySignatureError validate_policy(:Umbrella, [F], F, s)
        @test validate_policy(:Umbrella, [F], A, s) === nothing
        @test_throws PolicySignatureError validate_policy(:Other, [F], A, s)
        bad = FiniteKernel(FiniteSpace(F), FiniteSpace(A), [0.9 0.1; 0.9 0.5; 0.1 0.9]';
                           check=false)
        @test_throws PolicySignatureError validate_policy(:Umbrella, [F], A,
                                                          StochasticPolicy(:Umbrella, bad))
        two_out = FiniteKernel(FiniteSpace(F), FiniteSpace([A, A]), ones(2, 2, 3) ./ 4;
                               check=false)
        @test_throws PolicySignatureError StochasticPolicy(:Umbrella, two_out)
    end

    @testset "ConstantPolicy" begin
        c = ConstantPolicy(:take)
        k = policy_kernel(c, FiniteSpace(F), FiniteSpace(A))
        @test k.dom == FiniteSpace(F)
        @test all(probability(k, :take, f) == 1.0 for f in F.labels)
        k0 = policy_kernel(c, FiniteSpace(), FiniteSpace(A))
        @test k0 == point_mass(FiniteSpace(A), :take)
        @test validate_policy(:Umbrella, [F], A, c) === nothing
        @test_throws PolicySignatureError validate_policy(:Umbrella, [F], A,
                                                          ConstantPolicy(:fly))
        @test_throws PolicySignatureError policy_kernel(ConstantPolicy(:fly), FiniteSpace(),
                                                        FiniteSpace(A))
    end

    @testset "enumeration" begin
        @test n_deterministic_policies([F], A) == 8
        @test n_deterministic_policies(FiniteAxis[], A) == 2
        ps = all_deterministic_policies(:Umbrella, [F], A)
        @test length(ps) == 8
        @test allunique(ps)
        @test all(p -> p.information == [F] && p.action == A, ps)
        @test first(ps).table == [:take, :take, :take]
        @test last(ps).table == [:leave, :leave, :leave]
        m = umbrella_model()
        @test n_deterministic_policies(m, :Umbrella) == 8
        @test all_deterministic_policies(m, :Umbrella) == ps
        g = reference_grazing_model()
        @test n_deterministic_policies(g, :GrazingManagement) == 3^9
    end

    @testset "model helpers" begin
        m = umbrella_model()
        p = deterministic_policy(m, :Umbrella, f -> f == :rainy ? :take : :leave)
        @test p.information == [F] && p.action == A
        @test validate_policy(m, :Umbrella, p) === nothing
        @test policy_kernel(p, m, :Umbrella) == policy_kernel(p)
        @test information_space(m, :Umbrella) == FiniteSpace(F)
        @test action_space(m, :Umbrella) == FiniteSpace(A)
        @test policy_kernel(ConstantPolicy(:take), m, :Umbrella).dom == FiniteSpace(F)
    end

    @testset "n_deterministic_policies does not overflow" begin
        A = FiniteAxis(:A, [:a, :b])
        @test n_deterministic_policies(FiniteAxis[], A) == 2
        @test n_deterministic_policies([FiniteAxis(:I, [:x, :y, :z])], A) == 8
        # 7 binary information variables: 2^128, which wrapped to 0 in Int128
        big = [FiniteAxis(Symbol("I", i), [:t, :f]) for i in 1:7]
        n = n_deterministic_policies(big, A)
        @test n isa BigInt
        @test n == BigInt(2)^128
        e = try
            all_deterministic_policies(:D, big, A)
            nothing
        catch err
            err
        end
        @test e isa PolicySearchTooLargeError
        @test e.nstrategies == BigInt(2)^128
        @test occursin("340282366920938463463374607431768211456", sprint(showerror, e))
    end

    @testset "Strategy" begin
        σ = Strategy()
        @test length(σ) == 0
        @test !is_complete(σ, umbrella_diagram())
        @test missing_policies(σ, umbrella_diagram()) == [:Umbrella]
        σ = Strategy(:Umbrella => ConstantPolicy(:take))
        @test is_complete(σ, umbrella_diagram())
        @test haskey(σ, :Umbrella)
        @test σ[:Umbrella] == ConstantPolicy(:take)
        @test collect(keys(σ)) == [:Umbrella]
        @test policies(σ) == Dict{Symbol,AbstractPolicy}(:Umbrella => ConstantPolicy(:take))
        @test Strategy(Dict(:Umbrella => ConstantPolicy(:take))) == σ
        @test hash(Strategy(Dict(:Umbrella => ConstantPolicy(:take)))) == hash(σ)
        @test !is_complete(σ, two_stage_diagram())
        @test missing_policies(σ, two_stage_diagram()) == [:Test, :Drill]
        @test occursin("ConstantPolicy", sprint(show, σ))
    end

    @testset "strategy enumeration" begin
        # The order of the exhaustive search: `Iterators.product` over `decision_order`.
        function product_order(m)
            id = syntax(m)
            ds = decision_order(id)
            names_ = [decision_name(id, d) for d in ds]
            return [Strategy(Dict{Symbol,AbstractPolicy}(names_[i] => c[i]
                                                         for i in eachindex(ds)))
                    for c in
                        vec(collect(Iterators.product((all_deterministic_policies(m, d)
                                                       for d in ds)...)))]
        end
        for (m, n) in ((umbrella_model(), 8), (two_stage_model(), 2 * 2^6))
            id = syntax(m)
            it = all_deterministic_strategies(m)
            σs = collect(it)
            @test σs isa Vector{Strategy}
            @test n_deterministic_strategies(m) == n
            @test n_deterministic_strategies(m) isa BigInt
            @test length(it) == length(σs) == n
            @test n_deterministic_strategies(id) == n
            @test allunique(σs)
            @test all(σ -> is_complete(σ, id), σs)
            @test all(σ -> all(validate_policy(m, d, σ[d]) === nothing
                               for d in decision_names(id)), σs)
            @test σs == product_order(m)
            # The syntax form reads the same axes from the diagram.
            @test collect(all_deterministic_strategies(id)) == σs
            @test occursin("$n strategies", sprint(show, it))
            # The exhaustive optimum is the first maximum of this sequence.
            eus = [expected_utility(m, σ) for σ in σs]
            first_best = σs[findfirst(==(maximum(eus)), eus)]
            for backend in
                (ExhaustivePolicySearch(), ExhaustivePolicySearch(; brute_force=true))
                sol = optimize(m, backend)
                @test sol.strategy == first_best
                @test sol.expected_utility ≈ maximum(eus)
                @test sol.diagnostics.nstrategies == n
            end
        end
        # The first decision varies fastest.
        σs = collect(all_deterministic_strategies(two_stage_model()))
        @test policy_table(σs[1][:Test]) != policy_table(σs[2][:Test])
        @test policy_table(σs[1][:Drill]) == policy_table(σs[2][:Drill])
        # A diagram without decisions has one, empty, strategy.
        nod = influence_diagram(:X => [:a, :b]; utilities=[:U => :X])
        @test collect(all_deterministic_strategies(nod)) == [Strategy()]
        @test n_deterministic_strategies(nod) == 1
        # Equally named decisions appear once, the first in decision order defining the axes.
        dup = two_stage_diagram()
        set_subpart!(dup, decision_id(dup, :Drill), :decision_name, :Test)
        @test n_deterministic_strategies(dup) == 2
        σd = collect(all_deterministic_strategies(dup))
        @test length(σd) == 2 && all(σ -> collect(keys(σ)) == [:Test], σd)
        @test all(σ -> σ[:Test].action == BayesianNetworks.axis(dup, :Test) &&
                      isempty(σ[:Test].information), σd)
        # Too many strategies to enumerate: counted exactly, refused before any list is built.
        big = influence_diagram((Symbol("I", i) => [:t, :f] for i in 1:7)...,
                                :A => [:a, :b];
                                decisions=[:A => Tuple(Symbol("I", i) for i in 1:7)],
                                utilities=[:U => :A])
        @test n_deterministic_strategies(big) == BigInt(2)^128
        @test_throws PolicySearchTooLargeError all_deterministic_strategies(big)
    end
end
