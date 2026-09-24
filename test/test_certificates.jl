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
