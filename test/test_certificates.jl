function dve_certificate_model()
    id = influence_diagram(:D => [:a, :b], :X => [:x0, :x1],
                           :Y => [:y0, :y1, :y2], :W => [:w0, :w1];
                           mechanisms=[:Y => (:X, :X)],
                           decisions=[:D => :Y],
                           utilities=[:U => (:X, :D), :Constant => ()])
    Q = Rational{BigInt}
    raw = Array{Q}(undef, 2, 2, 3)
    raw[1, 1, :] = Q[1 // 2, 1 // 4, 1 // 4]
    raw[1, 2, :] = Q[0, 0, 1]
    raw[2, 1, :] = Q[1 // 8, 3 // 8, 1 // 2]
    raw[2, 2, :] = Q[1 // 4, 1 // 2, 1 // 4]
    tables = Dict(:X => Q[1 // 4, 3 // 4], :Y => raw, :W => Q[1 // 2, 1 // 2])
    utilities_ = Dict(:U => Q[1 -1; -2 3], :Constant => fill(Q(1 // 8)))
    m = InfluenceDiagramModel(id)
    for name in (:X, :Y, :W)
        m = bind_cpt(m, name => Float64.(tables[name]))
    end
    for name in (:U, :Constant)
        m = bind_utility(m, name => Float64.(utilities_[name]))
    end
    companions = Dict{Tuple{Symbol,Int,Tuple},Rational{BigInt}}()
    for (name, table) in tables
        mid = mechanism_of(syntax(m), name)
        for I in CartesianIndices(table)
            companions[(:cpt, mid, Tuple(I) .- 1)] = table[I]
        end
    end
    for (name, table) in utilities_
        uid = utility_id(syntax(m), name)
        for I in CartesianIndices(table)
            companions[(:utility, uid, Tuple(I) .- 1)] = table[I]
        end
    end
    return m, companions
end

function dve_certificate_cells(c)
    out = Any[]
    for m in c["mechanisms"]
        append!(out, m.cpt.entries)
        append!(out, m.factor.entries)
    end
    for u in c["utilities"]
        append!(out, u.table.entries)
    end
    return out
end

@testset "complete DVE model certificates" begin
    m, companion = dve_certificate_model()
    before = deepcopy(m)
    c = export_dve_certificate(m)
    @test c["format"] == "ecorecipes.dve-certificate" && c["version"] == 1
    @test c["numeric"] == (mode="binary64_exact", runtime_bits=true, normalization="none")
    @test c["provenance"].origin == "runtime" && c["provenance"].exact_source == "none"
    @test c["evidence"] == (hard=Any[], likelihood=nothing)
    @test [v.id for v in c["variables"]] == string.(variables(syntax(m)))
    @test [d.id for d in c["decisions"]] == string.(decisions(syntax(m)))
    @test c["decision_order"] == string.(decision_order(syntax(m)))
    @test m == before
    @test all(length(e.value.f64) == 16 for e in dve_certificate_cells(c))
    @test all(!haskey(e.value, :q) for e in dve_certificate_cells(c))
    @test length(dve_certificate_cells(c)) == 31
    @test_throws DVEExportError export_dve_certificate(m; max_entries=30)
    @test length(dve_certificate_cells(export_dve_certificate(m; max_entries=31))) == 31

    ys = string(variable_id(syntax(m), :Y))
    y = only(mm for mm in c["mechanisms"] if mm.target == ys)
    @test y.cpt.axes == ["2", "2", "3"]
    @test y.factor.axes == ["2", "3"]
    @test [Tuple(e.at) for e in y.cpt.entries] == sort([Tuple(e.at) for e in y.cpt.entries])
    raw = Dict(Tuple(e.at) => e.value for e in y.cpt.entries)
    @test all(e.value == raw[(e.at[1], e.at[1], e.at[2])] for e in y.factor.entries)
    @test all(u.table.axes == [slot.variable for slot in u.inputs] for u in c["utilities"])
    constant = only(u for u in c["utilities"] if u.name == "Constant")
    @test isempty(constant.table.axes) && only(constant.table.entries).at == Int[]

    exact = export_dve_certificate(m; numeric_mode=:rational_exact, exact_tables=companion)
    @test exact["provenance"].exact_source == "caller_companion"
    @test exact["numeric"].normalization == "none"
    @test [e.value.f64 for e in dve_certificate_cells(exact)] ==
          [e.value.f64 for e in dve_certificate_cells(c)]
    pure = export_dve_certificate(m; numeric_mode=:rational_exact, exact_tables=companion,
                                  capture_runtime_bits=false)
    @test all(haskey(e.value, :q) && !haskey(e.value, :f64)
              for e in dve_certificate_cells(pure))
    @test companion == last(dve_certificate_model())

    observed = observe(m, :W => :w1)
    ce = export_dve_certificate(observed)
    @test only(ce["evidence"].hard) == (variable="4", state_index=1)
    @test findfirst(==("4"), ce["topological_order"]) <
          findfirst(==("1"), ce["topological_order"])
    fixed = fix_decision(m, :D => :a)
    @test export_dve_certificate(fixed) == c
    intervention = export_dve_certificate(do_intervention(m, :W => :w1))
    @test any(p.reference.type == "PointMassRef" for p in intervention["reference_pool"])
    @test any(p.reference.type == "NoRef" for p in c["reference_pool"])
    @test any(p.reference.type == "NamedRef" for p in c["reference_pool"])

    changed = deepcopy(syntax(m))
    mid = mechanism_of(changed, :W)
    ref = PolicyRef(:opaque_policy)
    set_subpart!(changed, mid, :kernel_ref, ref)
    ks = copy(kernels(m))
    ks[ref] = kernel(m, :W)
    policy_ref_model = InfluenceDiagramModel(BayesModel(bayes_model(m); syntax=changed,
                                                        kernels=ks);
                                             utilities=bound_utilities(m))
    @test any(p.reference == (type="PolicyRef", decision="opaque_policy")
              for p in export_dve_certificate(policy_ref_model)["reference_pool"])

    empty = export_dve_certificate(InfluenceDiagramModel(influence_diagram());
                                   max_entries=0)
    @test isempty(empty["variables"]) && isempty(empty["mechanisms"]) &&
          isempty(empty["utilities"]) && isempty(empty["reference_pool"])
    @test JSON3.read(JSON3.write(c)).format == c["format"]
end

@testset "certificate profile and companion failures" begin
    m, companion = dve_certificate_model()
    for kwargs in ((trace=true,), (numeric_mode=:approximate,),
                   (capture_runtime_bits=false,), (numeric_mode=:rational_exact,),
                   (exact_tables=companion,), (max_entries=-1,), (atol=Inf,),
                   (probability_atol=1.0,), (atol=(-(big(1) // big(2)^2000)),),
                   (probability_atol=1 - big(1) // big(2)^2000,))
        @test_throws DVEExportError export_dve_certificate(m; kwargs...)
    end
    missing = copy(companion)
    delete!(missing, first(keys(missing)))
    @test_throws DVEExportError export_dve_certificate(m; numeric_mode=:rational_exact,
                                                       exact_tables=missing)
    extra = copy(companion)
    extra[(:cpt, 999, ())] = 1 // 1
    @test_throws DVEExportError export_dve_certificate(m; numeric_mode=:rational_exact,
                                                       exact_tables=extra)
    wrong = copy(companion)
    key = (:cpt, mechanism_of(syntax(m), :X), (0,))
    wrong[key] = 1 // 3
    e = try
        export_dve_certificate(m; numeric_mode=:rational_exact, exact_tables=wrong)
        nothing
    catch err
        err
    end
    @test e isa DVEExportError && e.code == :EXACT_COMPANION_MISMATCH
    @test e.owner_kind == :mechanism && e.coordinates == [0]
    @test occursin("captured Float64", sprint(showerror, e))

    unsupported = bind_kernel(m,
                              :X => cpt(FiniteAxis(:X, states(syntax(m), :X)),
                                        Float32[0.25, 0.75]))
    @test_throws DVEExportError export_dve_certificate(unsupported)
    bad_utility = bind_utility(m, :Constant => Inf)
    @test_throws DVEExportError export_dve_certificate(bad_utility)

    calls = Ref(0)
    callback = bind_utility(m, :U => ((x, d) -> (calls[] += 1; 2.0)))
    export_dve_certificate(callback)
    @test calls[] == 4
    calls[] = 0
    @test_throws DVEExportError export_dve_certificate(callback; max_entries=0)
    @test calls[] == 0
end

@testset "exact nearest-even companion checks" begin
    rounds = InfluenceDiagrams._dve_rounds_to
    @test rounds(big(1) // big(3), 1 / 3)
    @test !rounds(big(1) // big(3), nextfloat(1 / 3))
    @test rounds(big(0) // big(1), 0.0) && rounds(big(0) // big(1), -0.0)
    tiny = Rational{BigInt}(nextfloat(0.0))
    @test rounds(tiny / 2, 0.0) && !rounds(tiny / 2, -0.0)
    @test !rounds(tiny / 2, nextfloat(0.0))
    @test rounds(-tiny / 2, -0.0) && !rounds(-tiny / 2, 0.0)
    midpoint = (Rational{BigInt}(0.5) + Rational{BigInt}(nextfloat(0.5))) / 2
    @test rounds(midpoint, 0.5) && !rounds(midpoint, nextfloat(0.5))
    high = floatmax(Float64)
    @test rounds(Rational{BigInt}(high), high)
    overflow_midpoint = Rational{BigInt}(high) +
                        (Rational{BigInt}(high) - Rational{BigInt}(prevfloat(high))) / 2
    @test !rounds(overflow_midpoint, high)
end

# Exact companions of a Float64 model: the simplest rational within one ulp of each cell
# when it rounds back to the cell (which the exporter checks), else the cell's dyadic value.
function simple_rational(x::Float64)
    q = rationalize(BigInt, x)
    return InfluenceDiagrams._dve_rounds_to(q, x) ? q : Rational{BigInt}(x)
end

function rational_companions(m)
    id = syntax(m)
    out = Dict{Tuple{Symbol,Int,Tuple},Rational{BigInt}}()
    for mid in mechanisms(id)
        t = cpt(kernel(m, variable_name(id, target(id, mid))))
        for I in CartesianIndices(t)
            out[(:cpt, mid, Tuple(I) .- 1)] = simple_rational(t[I])
        end
    end
    for uid in utilities(id)
        t = utility_table(utility(m, utility_name(id, uid)),
                          InfluenceDiagrams._utility_axes(m, uid))
        for I in CartesianIndices(t)
            out[(:utility, uid, Tuple(I) .- 1)] = simple_rational(t[I])
        end
    end
    return out
end

# The exact value of a certificate cell: the rational when present, else the dyadic
# value of the binary64 word.
function certificate_number(v)
    haskey(v, :q) && return parse(BigInt, v.q.num) // parse(BigInt, v.q.den)
    return Rational{BigInt}(reinterpret(Float64, parse(UInt64, v.f64; base=16)))
end
certificate_f64(v) = reinterpret(Float64, parse(UInt64, v.f64; base=16))

# An independent reading of a serialized certificate: the exact expected utility of its
# recorded policies on its exact data, conditioned on its hard evidence, by depth-first
# enumeration in topological order. Also reports whether every CPT row sums to one.
function certificate_policy_value(c)
    vars = Dict(v.id => v for v in c.variables)
    index(v, state) = findfirst(s -> s.id == state, vars[v].states) - 1
    cells(t) = Dict(Tuple(e.at) => certificate_number(e.value) for e in t.entries)
    by_target = Dict(m.target => (m.cpt.axes, cells(m.cpt)) for m in c.mechanisms)
    by_action = Dict(p.action => (p.axes,
                                  Dict(Tuple(e.at) => index(p.action, e.action)
                                       for e in p.entries))
                     for p in c.solution.policies)
    evidence_ = Dict(h.variable => h.state_index for h in c.evidence.hard)
    utilities_ = [(u.table.axes, cells(u.table)) for u in c.utilities]
    order = collect(c.topological_order)
    normalised = all(c.mechanisms) do m
        sums = Dict{Tuple,Rational{BigInt}}()
        for (at, q) in cells(m.cpt)
            sums[at[1:(end - 1)]] = get(sums, at[1:(end - 1)], 0) + q
        end
        return all(==(1), values(sums))
    end
    x = Dict{String,Int}()
    total = Ref(zero(Rational{BigInt}))
    weighted = Ref(zero(Rational{BigInt}))
    function visit(k, p)
        if k > length(order)
            total[] += p
            weighted[] += p * sum(t[Tuple(x[a] for a in axes)] for (axes, t) in utilities_;
                                  init=zero(Rational{BigInt}))
            return nothing
        end
        v = order[k]
        for s in 0:(length(vars[v].states) - 1)
            haskey(evidence_, v) && evidence_[v] != s && continue
            x[v] = s
            q = if haskey(by_target, v)
                axes, t = by_target[v]
                t[Tuple(x[a] for a in axes)]
            else
                axes, t = by_action[v]
                t[Tuple(x[a] for a in axes)] == s ? one(Rational{BigInt}) :
                zero(Rational{BigInt})
            end
            iszero(q) || visit(k + 1, p * q)
        end
        delete!(x, v)
        return nothing
    end
    visit(1, one(Rational{BigInt}))
    return weighted[] / total[], normalised
end

# Check a version-2 certificate's solution against Julia's own `DecisionSolution`: the
# layout predicted by the label-order theorems, every policy entry, and the value.
function check_certificate_solution(m, c, reference::DecisionSolution; exact::Bool)
    id = syntax(m)
    c = JSON3.read(JSON3.write(c))
    s = c.solution
    @test c.version == 2 && endswith(c.provenance.exporter, "-v2")
    @test s.conditioned_on == "evidence.hard"
    @test s.arithmetic == (exact ? "exact_rational" : "binary64")
    @test [p.decision for p in s.policies] == [d.id for d in c.decisions]
    for (p, d) in zip(s.policies, c.decisions)
        @test p.action == d.action
        @test p.axes == [slot.variable for slot in d.information]
        variable(v) = only(x for x in c.variables if x.id == v)
        dims = Tuple(length(variable(v).states) for v in p.axes)
        lex = sort(vec([collect(Tuple(I) .- 1) for I in CartesianIndices(dims)]))
        @test [collect(e.at) for e in p.entries] == lex
        dname = decision_name(id, parse(Int, p.decision))
        table = policy_table(reference.strategy[dname])
        a = decision_variable(id, parse(Int, p.decision))
        @test size(table) == dims
        @test all(p.entries) do e
            label = table[(e.at .+ 1)...]
            chosen = only(st for st in variable(p.action).states if st.id == e.action)
            return chosen.label == String(label) &&
                   string(BayesianNetworks.state_ids(id, a)[findfirst(==(label),
                                                                      states(id, a))]) ==
                   e.action
        end
        @test all(e -> haskey(e.score, :q) == exact, p.entries)
    end
    @test [variable_name(id, parse(Int, v)) for v in s.elimination_order] ==
          reference.diagnostics.order
    value = certificate_f64(s.value)
    @test value === reference.expected_utility
    if exact
        q = certificate_number(s.value)
        @test BayesianNetworks._nearest_binary64(q) === value
        policy_value, normalised = certificate_policy_value(c)
        normalised && @test q == policy_value
    else
        eu = expected_utility(m, reference.strategy)
        @test abs(value - eu) <= 4 * eps(max(abs(value), abs(eu)))
    end
    return c
end

@testset "DVE certificates with the solution" begin
    v1 = joinpath(@__DIR__, "fixtures", "dve-certificate-v1")
    @testset "the option off is the version-1 certificate, byte for byte" begin
        # Captured before the solution profile existed. The exporter string carries the
        # package version, so a version bump must refresh these files.
        u = umbrella_model()
        @test JSON3.write(export_dve_certificate(u)) ==
              read(joinpath(v1, "umbrella.binary64.json"), String)
        @test JSON3.write(export_dve_certificate(u; solution=false)) ==
              read(joinpath(v1, "umbrella.binary64.json"), String)
        @test JSON3.write(export_dve_certificate(u; numeric_mode=:rational_exact,
                                                 exact_tables=rational_companions(u))) ==
              read(joinpath(v1, "umbrella.rational.json"), String)
        o = two_stage_model()
        @test JSON3.write(export_dve_certificate(o; numeric_mode=:rational_exact,
                                                 exact_tables=rational_companions(o),
                                                 capture_runtime_bits=false,
                                                 solution=false)) ==
              read(joinpath(v1, "oil_wildcatter.rational_nobits.json"), String)
    end

    models = ["umbrella" => umbrella_model(), "oil wildcatter" => two_stage_model(),
              "grazing" => reference_grazing_model(),
              "observed umbrella" => observe(umbrella_model(), :Forecast => :rainy),
              "repeated parents" => first(dve_certificate_model())]
    @testset "$name" for (name, m) in models
        v1 = export_dve_certificate(m)
        companions = name == "repeated parents" ? last(dve_certificate_model()) :
                     rational_companions(m)
        rational = (numeric_mode=:rational_exact, exact_tables=companions)
        float_ = optimize(m, DecisionVariableElimination())
        stable = optimize(m, DecisionVariableElimination(; stable=true))

        # binary64 mode: the default binary64 run, and the exact run on the dyadic cells
        c = check_certificate_solution(m, export_dve_certificate(m; solution=true), float_;
                                       exact=false)
        @test c.solution.data == "f64" && !c.solution.exact_fallback
        @test c.solution.backend.order == "MinFill" && !c.solution.backend.stable
        @test c.solution.backend.atol_f64 === nothing
        @test certificate_f64((f64=c.solution.backend.constancy_atol_f64,)) ==
              BayesianNetworks.DEFAULT_ATOL
        @test c.solution.julia_version == string(VERSION)
        full = export_dve_certificate(m; solution=true)
        @test all(k -> full[k] == v1[k],
                  setdiff(keys(v1), ["version", "provenance", "solution"]))
        @test full["provenance"].implementation_manifest_sha256 ==
              v1["provenance"].implementation_manifest_sha256
        c = check_certificate_solution(m,
                                       export_dve_certificate(m;
                                                              solution=DecisionVariableElimination(;
                                                                                                   stable=true)),
                                       stable; exact=true)
        @test c.solution.data == "f64" && c.solution.backend.stable

        # rational mode: the exact run reads the companions; the binary64 run the words
        exact = export_dve_certificate(m; rational...,
                                       solution=DecisionVariableElimination(; stable=true))
        q = JSON3.read(JSON3.write(exact))
        @test q.solution.data == "q" && q.solution.arithmetic == "exact_rational"
        policy_value, normalised = certificate_policy_value(q)
        @test normalised
        @test certificate_number(q.solution.value) == policy_value
        # These models have no near-ties, so the companion run picks the tables of the
        # stable run on the binary64 words, and the values agree within rounding.
        for (p, d) in zip(q.solution.policies, sort(decisions(syntax(m))))
            table = policy_table(stable.strategy[decision_name(syntax(m), d)])
            a = decision_variable(syntax(m), d)
            ids = BayesianNetworks.state_ids(syntax(m), a)
            labels_ = states(syntax(m), a)
            @test [e.action for e in p.entries] ==
                  [string(ids[findfirst(==(table[(e.at .+ 1)...]), labels_)])
                   for e in p.entries]
        end
        v = certificate_f64(q.solution.value)
        @test abs(v - stable.expected_utility) <= 4 * eps(abs(v))
        check_certificate_solution(m, export_dve_certificate(m; rational..., solution=true),
                                   float_; exact=false)
        nobits = export_dve_certificate(m; rational..., capture_runtime_bits=false,
                                        solution=DecisionVariableElimination(; stable=true))
        @test nobits["solution"] == exact["solution"]
    end

    @testset "underflowed evidence records the exact fallback" begin
        id = influence_diagram(:A => [:rare, :usual], :B => [:rare, :usual],
                               :D => [:leave, :act];
                               decisions=[:D => ()], utilities=[:Value => :D])
        m = bind_cpt(InfluenceDiagramModel(id), [:A => [1e-200, 1.0], :B => [1e-200, 1.0]])
        m = observe(bind_utility(m, :Value => [-2.0, 3.0]), [:A => :rare, :B => :rare])
        c = JSON3.read(JSON3.write(export_dve_certificate(m; solution=true)))
        @test c.solution.exact_fallback && c.solution.arithmetic == "exact_rational"
        @test certificate_number(c.solution.value) == 3 && c.solution.value.q.den == "1"
        @test length(c.evidence.hard) == 2
    end

    @testset "impossible combinations are typed" begin
        m, companion = dve_certificate_model()
        code(f) =
            try
                f()
                nothing
            catch err
                err isa DVEExportError ? err.code : err
            end
        @test code(() -> export_dve_certificate(m; solution=ExhaustivePolicySearch())) ==
              :UNSUPPORTED_SOLUTION_PROFILE
        for solution in (true, DecisionVariableElimination())
            @test code(() -> export_dve_certificate(m; numeric_mode=:rational_exact,
                                                    exact_tables=companion,
                                                    capture_runtime_bits=false,
                                                    solution)) ==
                  :UNSUPPORTED_SOLUTION_PROFILE
        end
        @test code(() -> export_dve_certificate(m; trace=true, solution=true)) ==
              :UNSUPPORTED_TRACE_PROFILE
        # The three rows of the policy of D count against the budget.
        @test code(() -> export_dve_certificate(m; max_entries=33, solution=true)) ==
              :RESOURCE_LIMIT
        @test export_dve_certificate(m; max_entries=34, solution=true)["version"] == 2
        @test export_dve_certificate(m; max_entries=31)["version"] == 1
        # Solver failures keep their own types: exact arithmetic rejects a tolerated
        # negative entry.
        negative = bind_cpt(m, :X => [-1e-12, 1 + 1e-12])
        @test export_dve_certificate(negative; solution=true)["version"] == 2
        @test code(() -> export_dve_certificate(negative;
                                                solution=DecisionVariableElimination(;
                                                                                     stable=true))) isa
              BayesianNetworkInference.FactorDomainError
    end
end
