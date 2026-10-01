@testset "DVE structural and scale-invariant contracts" begin
    function rare_evidence(scale)
        id = influence_diagram(:I => [:low, :high], :D => [:a, :b], :E => [:yes, :no];
                               mechanisms=[:E => (:I, :D)],
                               decisions=[:D => :I], utilities=[:U => :I])
        table = zeros(2, 2, 2)
        table[:, :, 1] = scale .* [1.0 0.01; 1.0 0.01]
        table[:, :, 2] = 1 .- table[:, :, 1]
        m = bind_cpt(InfluenceDiagramModel(id), [:I => [0.5, 0.5], :E => table])
        return observe(bind_utility(m, :U => [0.0, 100.0]), :E => :yes)
    end
    for scale in (1.0, 1e-12, 1e-100)
        m = rare_evidence(scale)
        e = try
            optimize(m)
            nothing
        catch err
            err
        end
        @test e isa IrregularDiagramError
        @test e.what == :evidence && e.decision == :D && e.variables == [:E]
        @test occursin("ExhaustivePolicySearch", sprint(showerror, e))
        exact = optimize(m, ExhaustivePolicySearch())
        @test exact.expected_utility ≈ 100 / 1.01
        @test expected_utility(m, exact.strategy) ≈ exact.expected_utility
    end

    i = FiniteAxis(:I, [:common, :rare])
    d = FiniteAxis(:D, [:a, :b])
    for scale in (1.0, 1e-12, 1e-100)
        bad = Valuation(Factor([i, d], [1.0 1.0; scale 2scale]))
        @test_throws IrregularDiagramError max_out(bad, :D)
        good = Valuation(Factor([i, d], [0.0 0.0; scale scale]))
        @test max_out(good, :D; atol=0)[1].φ.table == [0.0, scale]
    end
    for atol in (-1.0, NaN, Inf, 1.0)
        @test_throws ArgumentError DecisionVariableElimination(; atol)
        @test_throws ArgumentError max_out(Valuation(Factor(d, [1.0, 1.0])), :D; atol)
    end
    limited = influence_diagram(:A => [:a, :b], :B => [:a, :b];
                                decisions=[:A => Symbol[], :B => Symbol[]])
    m = InfluenceDiagramModel(limited)
    @test !is_no_forgetting(m)
    @test_throws IrregularDiagramError optimize(m)
    @test optimize(m, ExhaustivePolicySearch()).expected_utility == 0

    id = influence_diagram(:X => [:no, :yes], :Y => [:no, :yes], :D => [:a, :b];
                           mechanisms=[:Y => (:X, :X)], decisions=[:D => :Y],
                           utilities=[:U => (:X, :D)])
    table = zeros(2, 2, 2)
    for x1 in 1:2, x2 in 1:2
        table[x1, x2, x1 == x2 ? 2 : 1] = 1.0
    end
    repeated = bind_utility(bind_cpt(InfluenceDiagramModel(id),
                                     [:X => [0.4, 0.6], :Y => table]),
                            :U => [1.0 0.0; 0.0 2.0])
    dve = optimize(repeated)
    @test dve.expected_utility ≈
          optimize(repeated, ExhaustivePolicySearch()).expected_utility
    @test expected_utility(repeated, dve.strategy) ≈ dve.expected_utility
    @test Set(strong_elimination_order(repeated)) == Set([:X, :Y, :D])
end

@testset "expected utility forwards normalization tolerance" begin
    id = influence_diagram(:X => [:no, :yes], :D => [:a, :b];
                           decisions=[:D => Symbol[]], utilities=[:U => (:X, :D)])
    m = bind_utility(bind_cpt(InfluenceDiagramModel(id), :X => [0.5, 0.5000001];
                              atol=1e-6), :U => [0.0 1.0; 2.0 3.0])
    policy = optimize(m; atol=1e-6).strategy
    @test_throws BayesianNetworks.UnnormalizedKernelError expected_utility(m, policy)
    eu = expected_utility(m, policy; atol=1e-6)
    @test eu ≈ expected_utility(instantiate(m, policy; atol=1e-6); atol=1e-6)
    @test eu ≈
          optimize(m, ExhaustivePolicySearch(; brute_force=true);
                   atol=1e-6).expected_utility
    # Accepted rounded rows need not define an exactly normalized joint.
    @test eu ≈ optimize(m, ExhaustivePolicySearch(); atol=1e-6).expected_utility atol = 1e-6
    observed = observe(m, :X => :yes)
    @test expected_utility(observed, policy; atol=1e-6) ≈ 3.0
end

@testset "influence-diagram isomorphism keeps all parts" begin
    function duplicate_variables(reverse_order)
        order = reverse_order ? [:B, :A, :D] : [:A, :B, :D]
        id = influence_diagram((v => [:no, :yes] for v in order)...;
                               mechanisms=[:B => :A], decisions=[:D => :B],
                               utilities=[:U => (:B, :D)])
        for name in (:A, :B)
            set_subpart!(id, variable_id(id, name), :variable_name, :X)
        end
        return id
    end
    a, b = duplicate_variables(false), duplicate_variables(true)
    @test validate(a) === nothing && validate(b) === nothing
    @test canonicalize(a) != canonicalize(b)
    @test is_isomorphic(a, b) && is_isomorphic(b, a)
    @test_throws BayesianNetworks.ModelTooLargeError is_isomorphic(a, b; max_orderings=1)
    changed = deepcopy(b)
    set_subpart!(changed, 1, :utility_ref, NamedRef("different-utility"))
    @test !is_isomorphic(a, changed)
    changed = deepcopy(b)
    set_subpart!(changed, 1, :information_variable, 2)
    @test !is_isomorphic(a, changed)

    function duplicate_utilities(reverse_order)
        us = reverse_order ? [:Second => (:B, :D), :First => :A] :
             [:First => :A, :Second => (:B, :D)]
        id = influence_diagram(:A => [:no, :yes], :B => [:no, :yes], :D => [:a, :b];
                               mechanisms=[:B => :A], decisions=[:D => :B], utilities=us)
        set_subpart!(id, :utility_name, [:U, :U])
        return id
    end
    @test is_isomorphic(duplicate_utilities(false), duplicate_utilities(true))
end

# docs/LEAN-JULIA-DISCREPANCIES-2026-09-30.md, items 1 and 2: the Float64 path broke an exact
# signed-zero tie towards the second label, and accepted non-finite utilities.
@testset "Float64 DVE: signed-zero ties and non-finite utilities" begin
    id = influence_diagram(:Act => [:off, :on]; decisions=[:Act => ()],
                           utilities=[:Reward => :Act])
    # -0.0 and 0.0 are an exact tie, which resolves to the first label in both arithmetics,
    # as the Lean first-label selector proves.
    tie = bind_utility(InfluenceDiagramModel(id), :Reward => [-0.0, 0.0])
    for backend in
        (DecisionVariableElimination(), DecisionVariableElimination(; stable=true),
         ExhaustivePolicySearch(), ExhaustivePolicySearch(; brute_force=true))
        sol = optimize(tie, backend)
        @test sol.strategy[:Act]() == :off
        @test iszero(sol.expected_utility)
    end
    # A NaN or infinite utility has no expected value: every backend rejects it, as
    # `expected_utility` does.
    for bad in (NaN, Inf, -Inf)
        m = bind_utility(InfluenceDiagramModel(id), :Reward => [1.0, bad])
        for backend in (DecisionVariableElimination(),
                        DecisionVariableElimination(; stable=true),
                        ExhaustivePolicySearch(), ExhaustivePolicySearch(; brute_force=true))
            @test_throws UtilityScopeError optimize(m, backend)
        end
        @test_throws UtilityScopeError expected_utility(m, optimize(tie).strategy)
    end
end

# docs/LEAN-JULIA-DISCREPANCIES-2026-09-30.md, items 3, 4, 6 and 8: what the policy tables are.
@testset "DVE policy tables: rounding ties, exact guards, evidence, label order" begin
    # 3. The stored data tie exactly (both rows sum to 1 + 2^-52), so exact arithmetic picks
    # the first label; Float64 summation may round the tie either way, but its value is
    # within a few ulps of the exact one.
    id = influence_diagram(:Act => [:off, :on]; decisions=[:Act => ()],
                           utilities=[:U1 => :Act, :U2 => :Act, :U3 => :Act])
    m = bind_utility(InfluenceDiagramModel(id), :U1 => [2.0^-53, 2.0^-52])
    m = bind_utility(m, :U2 => [2.0^-53, 0.0])
    m = bind_utility(m, :U3 => [1.0, 1.0])
    exact = optimize(m, DecisionVariableElimination(; stable=true))
    @test exact.strategy[:Act]() == :off
    @test exact.expected_utility == 1 + 2.0^-52
    @test isapprox(optimize(m).expected_utility, exact.expected_utility; atol=4eps())

    # 4. An exactly normalised model passes the probability guard with exact equality.
    ih = influence_diagram(:H => [:low, :high], :Act => [:leave, :act];
                           decisions=[:Act => :H], utilities=[:U => (:H, :Act)])
    mh = bind_cpt(InfluenceDiagramModel(ih), :H => [0.25, 0.75])
    mh = bind_utility(mh, :U => [0.0 1.0; 2.0 0.5])
    sol = optimize(mh, DecisionVariableElimination(; stable=true, atol=0))
    @test sol.diagnostics.exact_probability_guards
    @test sol.expected_utility == optimize(mh, ExhaustivePolicySearch()).expected_utility

    # 6. With evidence on an information variable the policy does not read it: the row that
    # contradicts the evidence repeats the observed row, and the scope omits the variable.
    is = influence_diagram(:S => [:a, :b], :Act => [:off, :on]; decisions=[:Act => :S],
                           utilities=[:U => (:S, :Act)])
    ms = bind_cpt(InfluenceDiagramModel(is), :S => [0.5, 0.5])
    ms = observe(bind_utility(ms, :U => [1.0 0.0; 0.0 1.0]), :S => :a)
    so = optimize(ms)
    @test so.strategy[:Act](:a) == :off
    @test so.strategy[:Act](:b) == so.strategy[:Act](:a)
    @test so.diagnostics.policy_scopes[:Act] == Symbol[]
    @test so.expected_utility == 1.0

    # 8. The first label is the first in `state_position` order, not alphabetical: the
    # action axis DVE maximises over lists the states as declared.
    iz = influence_diagram(:Act => [:zeta, :alpha]; decisions=[:Act => ()],
                           utilities=[:U => :Act])
    mz = bind_utility(InfluenceDiagramModel(iz), :U => [1.0, 1.0])
    for backend in
        (DecisionVariableElimination(), DecisionVariableElimination(; stable=true))
        policy = optimize(mz, backend).strategy[:Act]
        @test policy() == :zeta
        @test policy.action.labels == [:zeta, :alpha]
    end
end
