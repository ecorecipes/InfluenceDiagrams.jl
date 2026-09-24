# The source authority of the version-1 proof-data contract, not the current checkout hash.
const _DVE_CERTIFICATE_SOURCE = "070b9b202f6e703b077b7527d47c1d53cab047fd969608ee733bc1308ccfa5c7"

function _dve_export_error(code, message, owner; at=())
    return throw(DVEExportError(code, owner.kind, owner.id, owner.name, collect(Int, at),
                                message))
end

function _dve_source_id(id::Integer, owner)
    1 <= id <= typemax(Int64) ||
        _dve_export_error(:STRUCTURAL_PRECONDITION,
                          "source part id is outside the v1 range", owner)
    return string(id)
end

function _dve_float_bits(x, owner; at=())
    x isa Float64 ||
        _dve_export_error(:UNSUPPORTED_SCALAR_TYPE,
                          "expected a materialized Float64 cell, got $(typeof(x))",
                          owner; at)
    isfinite(x) ||
        _dve_export_error(:UNSUPPORTED_SCALAR_TYPE, "nonfinite cells cannot be exported",
                          owner; at)
    return string(reinterpret(UInt64, x); base=16, pad=16)
end

function _dve_exact_value(x, owner, at)
    q = if x isa Integer && !(x isa Bool)
        BigInt(x) // BigInt(1)
    elseif x isa Rational
        denominator(x) > 0 ||
            _dve_export_error(:EXACT_COMPANION_MISMATCH, "the companion must be finite",
                              owner; at)
        BigInt(numerator(x)) // BigInt(denominator(x))
    else
        _dve_export_error(:EXACT_COMPANION_MISMATCH,
                          "companions must be integers or exact rationals",
                          owner; at)
    end
    n, d = numerator(q), denominator(q)
    ndigits(abs(n)) + (n < 0 ? 1 : 0) <= 4096 && ndigits(d) <= 4096 ||
        _dve_export_error(:RESOURCE_LIMIT,
                          "rational components exceed the v1 4096-character limit",
                          owner; at)
    return q
end

# Exact rational midpoints avoid double rounding, including subnormals and overflow edges.
function _dve_rounds_to(q::Rational{BigInt}, x::Float64)
    isfinite(x) || return false
    iszero(x) && !iszero(q) && ((q < 0) != signbit(x)) && return false
    center = Rational{BigInt}(x)
    before, after = prevfloat(x), nextfloat(x)
    lower = isfinite(before) ? (Rational{BigInt}(before) + center) / 2 :
            center - (Rational{BigInt}(after) - center) / 2
    upper = isfinite(after) ? (center + Rational{BigInt}(after)) / 2 :
            center + (center - Rational{BigInt}(before)) / 2
    even = iseven(reinterpret(UInt64, x))
    return (lower < q < upper) || (even && (q == lower || q == upper))
end

function _dve_companions(mode, tables, owner)
    if mode == :binary64_exact
        tables === nothing ||
            _dve_export_error(:UNSUPPORTED_NUMERIC_MODE,
                              "exact_tables requires rational_exact mode", owner)
        return nothing
    end
    tables isa AbstractDict ||
        _dve_export_error(:EXACT_COMPANION_MISMATCH,
                          "rational_exact requires an explicit complete exact_tables dictionary; no rationals are inferred from floats",
                          owner)
    result = Dict{Tuple{Symbol,Int,Tuple},Any}()
    for (key, value) in tables
        valid = key isa Tuple && length(key) == 3 &&
                key[1] in (:cpt, :utility) &&
                key[2] isa Integer && !(key[2] isa Bool) &&
                1 <= key[2] <= typemax(Int64) && key[3] isa Tuple &&
                all(i -> i isa Integer && !(i isa Bool) && 0 <= i <= 9007199254740991,
                    key[3])
        valid ||
            _dve_export_error(:EXACT_COMPANION_MISMATCH,
                              "invalid companion key $(repr(key))", owner)
        canonical = (key[1], Int(key[2]), Tuple(Int(i) for i in key[3]))
        result[canonical] = value
    end
    return result
end

function _dve_number(x, key, mode, capture_bits, companions, used, owner)
    bits = _dve_float_bits(x, owner; at=key[3])
    if mode == :binary64_exact
        return (f64=bits,)
    end
    haskey(companions, key) ||
        _dve_export_error(:EXACT_COMPANION_MISMATCH, "missing companion for $(repr(key))",
                          owner; at=key[3])
    push!(used, key)
    q = _dve_exact_value(companions[key], owner, key[3])
    _dve_rounds_to(q, x) ||
        _dve_export_error(:EXACT_COMPANION_MISMATCH,
                          "the exact companion does not round to the captured Float64 cell",
                          owner; at=key[3])
    rational = (num=string(numerator(q)), den=string(denominator(q)))
    return capture_bits ? (q=rational, f64=bits) : (q=rational,)
end

function _dve_reference!(pool, codes, ref::KernelRef, owner)
    key, payload = if ref isa NoRef
        (("NoRef", ""), (type="NoRef",))
    elseif ref isa NamedRef
        (("NamedRef", ref.id), (type="NamedRef", id=ref.id))
    elseif ref isa PointMassRef
        (("PointMassRef", String(ref.state)),
         (type="PointMassRef", state=String(ref.state)))
    elseif ref isa PolicyRef
        (("PolicyRef", String(ref.decision)),
         (type="PolicyRef", decision=String(ref.decision)))
    else
        _dve_export_error(:STRUCTURAL_PRECONDITION,
                          "unsupported reference type $(typeof(ref))", owner)
    end
    return get!(codes, key) do
        code = length(pool)
        push!(pool, (code=code, reference=payload))
        return code
    end
end

function _dve_slots(id, rows, position, variable, owner)
    return [(id=_dve_source_id(i, owner), position=subpart(id, i, position),
             variable=_dve_source_id(subpart(id, i, variable), owner)) for i in rows]
end

function _dve_numeric_table(axes, table, encode, owner)
    entries = Any[]
    # Reverse the iteration dimensions, not the table: the rightmost coordinate runs fastest.
    for reversed in CartesianIndices(reverse(size(table)))
        coordinate = reverse(Tuple(reversed))
        at = coordinate .- 1
        push!(entries, (at=collect(Int, at), value=encode(table[coordinate...], at)))
    end
    return (axes=[_dve_source_id(v, owner) for v in axes], entries=entries)
end

function _dve_export_budget(id, limit, owner)
    limit isa Bool &&
        _dve_export_error(:RESOURCE_LIMIT, "max_entries must be an integer count", owner)
    limit >= 0 ||
        _dve_export_error(:RESOURCE_LIMIT, "max_entries must be nonnegative", owner)
    cardinality(vs) = prod((BigInt(nstates(id, v)) for v in vs); init=BigInt(1))
    total = BigInt(0)
    for m in mechanisms(id)
        raw = vcat(inputs(id, m), target(id, m))
        total += cardinality(raw) + cardinality(unique(raw))
    end
    for u in utilities(id)
        total += cardinality(utility_scope(id, u))
    end
    total <= limit ||
        _dve_export_error(:RESOURCE_LIMIT,
                          "complete export needs $total numeric entries, limit is $limit",
                          owner)
    return nothing
end

function _dve_certificate_order(id, ev, owner)
    ancestors = Set(variable_id(id, name) for name in keys(ev))
    pending = collect(ancestors)
    while !isempty(pending)
        v = pop!(pending)
        for parent in parents(id, v)
            if !(parent in ancestors)
                push!(ancestors, parent)
                push!(pending, parent)
            end
        end
    end
    ds = decision_order(id)
    graph = information_graph(id)
    if !isempty(ds)
        first_action = decision_variable(id, first(ds))
        for v in ancestors
            add_edge!(graph, v, first_action)
        end
    end
    order, remaining = _kahn(graph)
    isempty(remaining) ||
        _dve_export_error(:STRUCTURAL_PRECONDITION,
                          "no combined order admits the evidence prefix", owner)
    ordered_decisions = [decision_of(id, v) for v in order if is_decision(id, v)]
    ordered_decisions == ds ||
        _dve_export_error(:STRUCTURAL_PRECONDITION,
                          "export order differs from runtime decision_order", owner)
    return order, ds
end

"""
    export_dve_certificate(m::InfluenceDiagramModel;
        numeric_mode=:binary64_exact, exact_tables=nothing,
        capture_runtime_bits=true, trace=false, max_entries=1_000_000,
        atol=DEFAULT_ATOL, probability_atol=1e-9,
        model_name="InfluenceDiagramModel") -> Dict{String,Any}

Capture complete model data in the version-1 `ecorecipes.dve-certificate`
profile. Original source part IDs are decimal strings; semantic slots retain
their position order and every table entry has explicit zero-based coordinates
in lexicographic order. Raw ordered CPTs and the actual unique-scope diagonal
factors are both captured. Evidence ancestors are placed before the first
decision in a compatible combined dependency order.

`binary64_exact` preserves each finite materialized Float64 cell's raw bits.
`rational_exact` requires a complete caller-supplied dictionary keyed by
`(:cpt, mechanism_id, coordinates)` and `(:utility, utility_id, coordinates)`.
Companions must be exact integers/rationals whose nearest-even Float64 rounding
matches the captured cell. No approximate rationalization or normalization is
performed. Other raw kernel scalar types and `trace=true` are unsupported in v1.

Structure and kernel arrays are copied before capture, and each utility table is
materialized once. The caller must not mutate the model, companion dictionary or
external callback state during export. The current strategy is not an optimization
constraint in the payload. `max_entries` counts raw CPT, factor and utility cells;
resource failure occurs before utility callbacks are evaluated.

The source-manifest field identifies the frozen v1 theorem/data contract, not
the installed package's commit. Captured tolerances are metadata, not proof
premises; finite in-range tolerance arguments are converted to Float64 and
those captured values are used for validation. Exact dyadic rows may fail
exact normalization despite runtime tolerance
acceptance; the reference consumer reports theorem applicability separately.
The certificate is model data, not a verified production execution trace or a
proof of the Julia exporter/compiler. See `docs/src/certificates.md`.
"""
function export_dve_certificate(m::InfluenceDiagramModel;
                                numeric_mode::Symbol=:binary64_exact,
                                exact_tables=nothing,
                                capture_runtime_bits::Bool=true,
                                trace::Bool=false,
                                max_entries::Integer=1_000_000,
                                atol::Real=BayesianNetworks.DEFAULT_ATOL,
                                probability_atol::Real=1e-9,
                                model_name::AbstractString="InfluenceDiagramModel")
    owner = (kind=:model, id=nothing, name=String(model_name))
    trace && _dve_export_error(:UNSUPPORTED_TRACE_PROFILE,
                               "version 1 contains model data, not traces", owner)
    numeric_mode in (:binary64_exact, :rational_exact) ||
        _dve_export_error(:UNSUPPORTED_NUMERIC_MODE,
                          "unknown numeric_mode $(repr(numeric_mode))", owner)
    numeric_mode == :binary64_exact && !capture_runtime_bits &&
        _dve_export_error(:UNSUPPORTED_NUMERIC_MODE,
                          "binary64_exact requires captured bits", owner)
    normalization_tol, decision_tol = Float64(atol), Float64(probability_atol)
    isfinite(atol) && atol >= 0 && isfinite(normalization_tol) && normalization_tol >= 0 ||
        _dve_export_error(:STRUCTURAL_PRECONDITION,
                          "kernel tolerance must be finite and nonnegative", owner)
    isfinite(probability_atol) && 0 <= probability_atol < 1 &&
        isfinite(decision_tol) && 0 <= decision_tol < 1 ||
        _dve_export_error(:STRUCTURAL_PRECONDITION,
                          "decision tolerance must be finite and in [0,1)", owner)
    validate(syntax(m); closed=true, unique_names=true)
    _dve_export_budget(syntax(m), max_entries, owner)
    companions = _dve_companions(numeric_mode, exact_tables, owner)
    used = Set{Tuple{Symbol,Int,Tuple}}()
    bm = BayesModel(m.model; syntax=deepcopy(syntax(m)), spaces=deepcopy(spaces(m)),
                    kernels=deepcopy(kernels(m)), evidence=copy(evidence(m)))
    snapshot = _with(m; model=bm, utilities=copy(bound_utilities(m)))
    _check_solvable(snapshot; atol=normalization_tol)
    id = syntax(snapshot)
    _check_dve_structure(id, evidence(snapshot))
    order, ds = _dve_certificate_order(id, evidence(snapshot), owner)
    pool = Any[]
    codes = Dict{Tuple{String,String},Int}()
    vars = [(id=_dve_source_id(v, owner), name=String(variable_name(id, v)),
             kind=is_decision(id, v) ? "decision" : "chance",
             space_ref=_dve_reference!(pool, codes, subpart(id, v, :space_ref), owner),
             states=[(id=_dve_source_id(s, owner), position=subpart(id, s, :state_position),
                      label=String(subpart(id, s, :state_name)))
                     for s in BayesianNetworks.state_ids(id, v)])
            for v in sort(variables(id))]
    mechs = Any[]
    for mid in sort(mechanisms(id))
        context = (kind=:mechanism, id=mid, name=String(mechanism_name(id, mid)))
        ref = kernel_ref(id, mid)
        ref isa NoRef &&
            _dve_export_error(:UNRESOLVED_BINDING,
                              "v1 requires a non-NoRef mechanism reference", context)
        target_id = target(id, mid)
        ps = inputs(id, mid)
        k = kernel(snapshot.model, variable_name(id, target_id))
        length(k.dom.axes) == length(ps) && length(k.codom.axes) == 1 &&
            all(labels(k.dom.axes[i]) == states(id, ps[i]) for i in eachindex(ps)) &&
            labels(only(k.codom.axes)) == states(id, target_id) ||
            _dve_export_error(:STRUCTURAL_PRECONDITION,
                              "kernel axes disagree with ordered source states", context)
        raw = copy(cpt(k))
        raw_axes = vcat(ps, target_id)
        encode = (x, at) -> _dve_number(x, (:cpt, mid, at), numeric_mode,
                                        capture_runtime_bits, companions, used, context)
        raw_table = _dve_numeric_table(raw_axes, raw, encode, context)
        factor = Factor(k, Symbol[variable_name(id, p) for p in ps],
                        variable_name(id, target_id))
        factor_axes = [variable_id(id, name) for name in factor.vars]
        factor_axes == unique(raw_axes) ||
            _dve_export_error(:STRUCTURAL_PRECONDITION,
                              "compiled factor scope disagrees with raw CPT", context)
        positions = Dict(v => i for (i, v) in enumerate(factor_axes))
        encode_factor = function (x, at)
            raw_at = Tuple(at[positions[v]] for v in raw_axes)
            original = raw[(raw_at .+ 1)...]
            _dve_float_bits(x, context; at) ==
            _dve_float_bits(original, context; at=raw_at) ||
                _dve_export_error(:EXACT_COMPANION_MISMATCH,
                                  "compiled factor is not the raw CPT diagonal",
                                  context; at)
            return encode(x, raw_at)
        end
        push!(mechs,
              (id=_dve_source_id(mid, context), name=context.name,
               target=_dve_source_id(target_id, context),
               kernel_ref=_dve_reference!(pool, codes, ref, context),
               parents=_dve_slots(id, BayesianNetworks.input_ids(id, mid),
                                  :input_position, :input_variable, context),
               cpt=raw_table,
               factor=_dve_numeric_table(factor_axes, factor.table, encode_factor, context)))
    end
    decs = [(id=_dve_source_id(d, owner), name=String(decision_name(id, d)),
             action=_dve_source_id(decision_variable(id, d), owner),
             information=_dve_slots(id, information_ids(id, d), :information_position,
                                    :information_variable, owner))
            for d in sort(decisions(id))]
    prec = [(id=_dve_source_id(p, owner),
             earlier=_dve_source_id(subpart(id, p, :earlier), owner),
             later=_dve_source_id(subpart(id, p, :later), owner))
            for p in sort(collect(parts(id, :DecisionPrecedence)))]
    us = Any[]
    for uid in sort(utilities(id))
        context = (kind=:utility, id=uid, name=String(utility_name(id, uid)))
        table = copy(utility_table(utility(snapshot, utility_name(id, uid)),
                                   _utility_axes(snapshot, uid)))
        encode = (x, at) -> _dve_number(x, (:utility, uid, at), numeric_mode,
                                        capture_runtime_bits, companions, used, context)
        push!(us,
              (id=_dve_source_id(uid, context), name=context.name,
               utility_ref=_dve_reference!(pool, codes, utility_ref(id, uid), context),
               inputs=_dve_slots(id, utility_input_ids(id, uid), :utility_position,
                                 :utility_variable, context),
               table=_dve_numeric_table(utility_scope(id, uid), table, encode, context)))
    end
    if companions !== nothing && used != Set(keys(companions))
        _dve_export_error(:EXACT_COMPANION_MISMATCH, "exact_tables contains unused entries",
                          owner)
    end
    hard = [(variable=_dve_source_id(v, owner),
             state_index=label_index(axis(id, v),
                                     evidence(snapshot)[variable_name(id, v)]) - 1)
            for v in sort([variable_id(id, name) for name in keys(evidence(snapshot))])]
    return Dict{String,Any}("format" => "ecorecipes.dve-certificate", "version" => 1,
                            "provenance" => (implementation_manifest_sha256=_DVE_CERTIFICATE_SOURCE,
                                             model_name=String(model_name),
                                             exporter="InfluenceDiagrams.jl/$(pkgversion(@__MODULE__))/export_dve_certificate-v1",
                                             origin="runtime",
                                             exact_source=numeric_mode == :binary64_exact ?
                                                          "none" :
                                                          "caller_companion"),
                            "numeric" => (mode=String(numeric_mode),
                                          runtime_bits=capture_runtime_bits,
                                          normalization="none"),
                            "runtime_tolerances" => (kernel_normalization_f64=_dve_float_bits(normalization_tol,
                                                                                              owner),
                                                     decision_probability_f64=_dve_float_bits(decision_tol,
                                                                                              owner)),
                            "reference_pool" => pool, "variables" => vars,
                            "topological_order" => [_dve_source_id(v, owner) for v in order],
                            "decision_order" => [_dve_source_id(d, owner) for d in ds],
                            "mechanisms" => mechs, "decisions" => decs,
                            "precedence" => prec,
                            "utilities" => us,
                            "evidence" => (hard=hard, likelihood=nothing))
end
