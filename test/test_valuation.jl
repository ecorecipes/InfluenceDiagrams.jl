@testset "Valuation algebra" begin
    A = FiniteAxis(:A, [:a0, :a1])
    B = FiniteAxis(:B, [:b0, :b1])
    D = FiniteAxis(:D, [:d0, :d1])
    pa = Factor([A], [0.4, 0.6])
    pb = Factor([A, B], [0.9 0.1; 0.2 0.8])
    u = Factor([B, D], [1.0 5.0; 10.0 2.0])

    @testset "construction and scope" begin
        v = Valuation(pa)
        @test v.φ == pa
        @test size(v.ψ.table) == () && v.ψ.table[] == 0
        @test scope(v) == [:A]
        w = Valuation(BayesianNetworkInference.unit_factor(), u)
        @test scope(w) == [:B, :D]
        @test occursin("Valuation", sprint(show, w))
        @test v == Valuation(pa)
        @test v ≈ Valuation(pa)
    end

    @testset "combine" begin
        v = combine(Valuation(pa), Valuation(pb))
        @test v.φ ≈ pa * pb
        @test all(iszero, v.ψ.table)
        w = combine(v, Valuation(BayesianNetworkInference.unit_factor(), u))
        @test Set(scope(w)) == Set([:A, :B, :D])
        @test w.ψ == u   # ψ broadcast: 0 + u
        # ψ addition broadcasts over the union scope
        u2 = Factor([A], [100.0, 200.0])
        z = combine(Valuation(BayesianNetworkInference.unit_factor(), u),
                    Valuation(BayesianNetworkInference.unit_factor(), u2))
        @test Set(z.ψ.vars) == Set([:A, :B, :D])
        t = BayesianNetworkInference.reorder(z.ψ, [:A, :B, :D]).table
        @test t[1, 2, 1] == 10.0 + 100.0
        @test t[2, 1, 2] == 5.0 + 200.0
        @test combine(Valuation[]).φ == BayesianNetworkInference.unit_factor()
    end

    @testset "sum_out" begin
        v = combine(Valuation(pa), Valuation(pb),
                    Valuation(BayesianNetworkInference.unit_factor(), u))
        s = sum_out(v, :B)
        @test !(:B in scope(s))
        # φ' = P(A); ψ' = E[u | A, D]
        @test s.φ ≈ pa
        expected = zeros(2, 2)   # (A, D)
        for a in 1:2, d in 1:2
            expected[a, d] = sum(pb.table[a, b] * u.table[b, d] for b in 1:2)
        end
        @test BayesianNetworkInference.reorder(s.ψ, [:A, :D]).table ≈ expected
        # eliminating a variable outside the scope is the identity
        @test sum_out(s, :Z) == s
        # 0/0 := 0
        zero_pa = Valuation(Factor([A], [0.0, 1.0]))
        s2 = sum_out(combine(zero_pa, Valuation(pb),
                             Valuation(BayesianNetworkInference.unit_factor(), u)),
                     :B)
        @test all(isfinite, s2.ψ.table)
        # a ψ variable absent from φ: ψ' = mean over the variable
        s3 = sum_out(Valuation(BayesianNetworkInference.unit_factor(), u), :B)
        @test s3.ψ.table ≈ vec(sum(u.table; dims=1)) ./ 2
        @test s3.φ.table[] == 2.0
    end

    @testset "max_out" begin
        v = combine(Valuation(pa), Valuation(pb),
                    Valuation(BayesianNetworkInference.unit_factor(), u))
        s = sum_out(v, :B)
        r, policy, pscope = max_out(s, :D)
        @test pscope == [:A]
        @test !(:D in scope(r))
        ψ = BayesianNetworkInference.reorder(s.ψ, [:A, :D]).table
        @test r.ψ.table ≈ vec(maximum(ψ; dims=2))
        @test policy == [ψ[a, 1] >= ψ[a, 2] ? :d0 : :d1 for a in 1:2]
        # the probability potential is not constant in D: irregular
        bad = Valuation(Factor([D], [0.3, 0.7]), u)
        @test_throws IrregularDiagramError max_out(bad, :D)
        # D only in φ (constant): first label, empty scope
        const_φ = Valuation(Factor([D], [0.5, 0.5]))
        r2, policy2, pscope2 = max_out(const_φ, :D)
        @test pscope2 == Symbol[] && policy2[] == :d0
        @test r2.φ.table[] == 0.5
        @test_throws BayesianNetworkInference.ScopeError max_out(Valuation(pa), :D)
        # ties resolve to the first label
        tie = Valuation(BayesianNetworkInference.unit_factor(), Factor([D], [3.0, 3.0]))
        @test max_out(tie, :D)[2][] == :d0
    end
end
