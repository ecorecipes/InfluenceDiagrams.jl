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

function _dve_export_budget(id, limit, owner; solution::Bool=false)
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
    if solution
        for d in decisions(id)
            total += cardinality(decision_information(id, d))
        end
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

# The solution profile (version 2)
##################################

function _dve_solution_backend(solution, numeric_mode, capture_runtime_bits, owner)
    solution === false && return nothing
    backend = solution === true ? DecisionVariableElimination() : solution
    backend isa DecisionVariableElimination ||
        _dve_export_error(:UNSUPPORTED_SOLUTION_PROFILE,
                          "the solution profile records a DecisionVariableElimination run, not $(nameof(typeof(backend)))",
                          owner)
    numeric_mode == :rational_exact && !capture_runtime_bits && !backend.stable &&
        _dve_export_error(:UNSUPPORTED_SOLUTION_PROFILE,
                          "a binary64 solution reads the Float64 cells, which capture_runtime_bits=false leaves out; use DecisionVariableElimination(stable=true)",
                          owner)
    return backend
end

# A solution number: `{f64}` for a binary64 run, `{q, f64}` for an exact one, where `f64`
# is the nearest-even rounding of `q`, as for an exported cell.
function _dve_solution_number(x, owner; at=())
    x isa Float64 && return (f64=_dve_float_bits(x, owner; at),)
    x isa Rational{BigInt} ||
        _dve_export_error(:UNSUPPORTED_SCALAR_TYPE,
                          "expected a Float64 or exact rational solution value, got $(typeof(x))",
                          owner; at)
    n, d = numerator(x), denominator(x)
    ndigits(abs(n)) + (n < 0 ? 1 : 0) <= 4096 && ndigits(d) <= 4096 ||
        _dve_export_error(:RESOURCE_LIMIT,
                          "solution rational components exceed the 4096-character limit",
                          owner; at)
    rounded = _nearest_binary64(x)
    isfinite(rounded) ||
        _dve_export_error(:UNSUPPORTED_SCALAR_TYPE,
                          "the exact solution value has no finite binary64 rounding",
                          owner; at)
    return (q=(num=string(n), den=string(d)), f64=_dve_float_bits(rounded, owner; at))
end

# What the run reports at each maximisation: the reduced utility potential of the
# decision's bucket, or `nothing` when no valuation mentions the action.
mutable struct _DVESolutionRecorder
    scores::Dict{Symbol,Any}
    final::Any
end
_DVESolutionRecorder() = _DVESolutionRecorder(Dict{Symbol,Any}(), nothing)

function (recorder::_DVESolutionRecorder)(kind::Symbol, value)
    if kind == :decision
        recorder.scores[value.decision] = value.result.ψ
    elseif kind == :inactive
        recorder.scores[value.decision] = nothing
    elseif kind == :final
        recorder.final = value
    end
    return nothing
end

# The maximal score of the row `coordinate` (one-based, one entry per information slot).
function _dve_row_score(score, info_axes, coordinate, zero_score, owner)
    score === nothing && return zero_score
    names = [axis.name for axis in info_axes]
    index = map(eachindex(score.vars)) do k
        j = findfirst(==(score.vars[k]), names)
        j === nothing &&
            _dve_export_error(:STRUCTURAL_PRECONDITION,
                              "the maximised utility potential depends on $(score.vars[k]), which is not observed",
                              owner)
        return label_index(score.axes[k], info_axes[j].labels[coordinate[j]])
    end
    return score.table[index...]
end

function _dve_solution(snapshot, backend, data, sources, normalization_tol, owner)
    id = syntax(snapshot)
    constancy = backend.atol === nothing ? normalization_tol : backend.atol
    _check_probability_tolerance(constancy)
    recorder = _DVESolutionRecorder()
    sol = _run_decision_elimination(snapshot, backend.order, constancy, normalization_tol,
                                    backend.stable; observer=recorder,
                                    sources=(kind, name) -> sources[(kind, name)])
    final = recorder.final
    exact = eltype(final.ψ.table) == Rational{BigInt}
    meu = only(final.ψ.table)
    exact || meu === sol.expected_utility ||
        _dve_export_error(:STRUCTURAL_PRECONDITION,
                          "the recorded value is not the run's expected utility", owner)
    value = _dve_solution_number(meu, owner)
    value.f64 == _dve_float_bits(sol.expected_utility, owner) ||
        _dve_export_error(:STRUCTURAL_PRECONDITION,
                          "the exact value does not round to the run's expected utility",
                          owner)
    zero_score = zero(eltype(final.ψ.table))
    policies_ = Any[]
    for d in sort(decisions(id))
        dname = decision_name(id, d)
        context = (kind=:decision, id=d, name=String(dname))
        p = sol.strategy[dname]
        info = decision_information(id, d)
        a = decision_variable(id, d)
        # The label order of the Lean label-order theorems: information slots in
        # `information_position` order, every axis in `state_position` order.
        p isa DeterministicPolicy &&
            [axis.name for axis in p.information] == [variable_name(id, v) for v in info] &&
            all(p.information[j].labels == states(id, info[j]) for j in eachindex(info)) &&
            p.action.name == variable_name(id, a) && p.action.labels == states(id, a) ||
            _dve_export_error(:STRUCTURAL_PRECONDITION,
                              "the policy table axes are not the information slots in state_position order",
                              context)
        action_states = BayesianNetworks.state_ids(id, a)
        score = recorder.scores[dname]
        entries = Any[]
        dims = Tuple(nstates(id, v) for v in info)
        for reversed in CartesianIndices(reverse(dims))
            coordinate = reverse(Tuple(reversed))
            at = coordinate .- 1
            chosen = action_states[label_index(p.action, p.table[coordinate...])]
            row = _dve_row_score(score, p.information, coordinate, zero_score, context)
            push!(entries,
                  (at=collect(Int, at), action=_dve_source_id(chosen, context),
                   score=_dve_solution_number(row, context; at)))
        end
        push!(policies_,
              (decision=_dve_source_id(d, context), action=_dve_source_id(a, context),
               axes=[_dve_source_id(v, context) for v in info],
               scope=[_dve_source_id(variable_id(id, x), context)
                      for x in sol.diagnostics.policy_scopes[dname]],
               entries=entries))
    end
    return (backend=(name="DecisionVariableElimination",
                     order=string(nameof(typeof(backend.order))), stable=backend.stable,
                     atol_f64=backend.atol === nothing ? nothing :
                              _dve_float_bits(backend.atol, owner),
                     constancy_atol_f64=_dve_float_bits(constancy, owner)),
            arithmetic=exact ? "exact_rational" : "binary64", data=String(data),
            exact_fallback=get(sol.diagnostics, :exact_fallback, false),
            conditioned_on="evidence.hard", julia_version=string(VERSION),
            elimination_order=[_dve_source_id(variable_id(id, x), owner)
                               for x in sol.diagnostics.order],
            value=value, policies=policies_)
end

"""
    export_dve_certificate(m::InfluenceDiagramModel;
        numeric_mode=:binary64_exact, exact_tables=nothing,
        capture_runtime_bits=true, trace=false, max_entries=1_000_000,
        atol=DEFAULT_ATOL, probability_atol=1e-9,
        model_name="InfluenceDiagramModel", solution=false) -> OrderedDict{String,Any}

Capture complete model data in the version-1 `ecorecipes.dve-certificate`
profile. The result is an `OrderedDict` (OrderedCollections' type, which
`BayesianNetworks` also returns for its CatColab documents) whose keys, and the
fields of every object inside it, follow the JSON Schema's property order, so
the key order `JSON3.write` emits does not depend on Julia's string hashing. It
is indexed like a `Dict`, and `==` ignores the key order. Original source part IDs are decimal strings; semantic slots retain
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

# Recording the solution (version 2)

With the default `solution=false` the result is the version-1 certificate,
byte for byte. `solution=true` runs `DecisionVariableElimination()`, and
`solution=backend` runs that `DecisionVariableElimination` backend; either
emits version 2: the version-1 fields unchanged (except `version` and the
`-v2` exporter suffix) plus a `"solution"` object recording that run's output.

The run is the production driver of [`decision_elimination`](@ref), with its
binary64 path and exact-rational fallback, or with `stable=true` its exact
rational path. It reads the certificate's own cells: the compiled factors and
materialized utility tables exported above (utility callbacks are not called
again). A binary64 run and an exact run in `binary64_exact` mode read the
`f64` words (the exact run their dyadic values; `data = "f64"`). An exact run
in `rational_exact` mode reads the rational companions (`data = "q"`). The run
conditions on the hard evidence rows of `evidence` and on nothing else; the
model's current strategy is ignored. Its normalization tolerance is
`runtime_tolerances.kernel_normalization_f64`, its constancy tolerance is the
backend's `atol`, or that normalization tolerance when `atol` is `nothing`.

The `solution` object holds the `backend` (order strategy name, `stable`,
`atol_f64`, `constancy_atol_f64`), the `arithmetic` (`"binary64"` or
`"exact_rational"`), `data`, `exact_fallback`, `conditioned_on =
"evidence.hard"`, `julia_version`, the `elimination_order` the run actually
used (variable IDs), the `value`, and one `policies` row per decision in
decision-ID order. A policy row names the `decision`, its `action` variable,
the information variables as `axes` in `information_position` order and the
variables its table really depends on as `scope`. Its `entries` cover every
information configuration, with zero-based `at` coordinates in each axis's
`state_position` order, lexicographic with the rightmost fastest; each entry
gives the chosen `action` as a state ID and the row's maximal `score`, the
run's bucket utility maximized over the action (zero when no valuation
mentions the action). A binary64 run writes numbers as `{f64}`, an exact run as
`{q, f64}` with `f64` the nearest-even rounding of `q`.

The solution is the output of one run, not a trusted optimality flag: it
claims only that this Julia run returned these tables and this value. Whether
they are optimal for the certificate's model is for a checker to decide. A
binary64 run's tables can differ from the exact ones near ties. Backends other
than `DecisionVariableElimination`, and a binary64 run on a `rational_exact`
certificate without `capture_runtime_bits`, whose `f64` cells it would need,
raise `DVEExportError` with code `:UNSUPPORTED_SOLUTION_PROFILE`. Every policy
row counts against `max_entries`. Solver failures keep their own exceptions.
"""
function export_dve_certificate(m::InfluenceDiagramModel;
                                numeric_mode::Symbol=:binary64_exact,
                                exact_tables=nothing,
                                capture_runtime_bits::Bool=true,
                                trace::Bool=false,
                                max_entries::Integer=1_000_000,
                                atol::Real=BayesianNetworks.DEFAULT_ATOL,
                                probability_atol::Real=1e-9,
                                model_name::AbstractString="InfluenceDiagramModel",
                                solution::Union{Bool,DecisionBackend}=false)
    owner = (kind=:model, id=nothing, name=String(model_name))
    trace && _dve_export_error(:UNSUPPORTED_TRACE_PROFILE,
                               "versions 1 and 2 contain model data and a result, not traces",
                               owner)
    numeric_mode in (:binary64_exact, :rational_exact) ||
        _dve_export_error(:UNSUPPORTED_NUMERIC_MODE,
                          "unknown numeric_mode $(repr(numeric_mode))", owner)
    numeric_mode == :binary64_exact && !capture_runtime_bits &&
        _dve_export_error(:UNSUPPORTED_NUMERIC_MODE,
                          "binary64_exact requires captured bits", owner)
    backend = _dve_solution_backend(solution, numeric_mode, capture_runtime_bits, owner)
    data = backend !== nothing && backend.stable && numeric_mode == :rational_exact ? :q :
           :f64
    run_inputs = Dict{Tuple{Symbol,Symbol},Factor}()
    normalization_tol, decision_tol = Float64(atol), Float64(probability_atol)
    isfinite(atol) && atol >= 0 && isfinite(normalization_tol) && normalization_tol >= 0 ||
        _dve_export_error(:STRUCTURAL_PRECONDITION,
                          "kernel tolerance must be finite and nonnegative", owner)
    isfinite(probability_atol) && 0 <= probability_atol < 1 &&
        isfinite(decision_tol) && 0 <= decision_tol < 1 ||
        _dve_export_error(:STRUCTURAL_PRECONDITION,
                          "decision tolerance must be finite and in [0,1)", owner)
    validate(syntax(m); closed=true, unique_names=true)
    _dve_export_budget(syntax(m), max_entries, owner; solution=backend !== nothing)
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
        if backend !== nothing
            run_inputs[(:chance, variable_name(id, target_id))] = if data == :q
                exact_cell = function (I)
                    raw_at = Tuple((Tuple(I) .- 1)[positions[v]] for v in raw_axes)
                    return _dve_exact_value(companions[(:cpt, mid, raw_at)], context,
                                            raw_at)
                end
                Factor(factor.vars, factor.axes,
                       Rational{BigInt}[exact_cell(I)
                                        for I in CartesianIndices(factor.table)])
            else
                factor
            end
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
        utility_axes = _utility_axes(snapshot, uid)
        table = copy(utility_table(utility(snapshot, utility_name(id, uid)), utility_axes))
        if backend !== nothing
            exact_table = data == :q ?
                          Rational{BigInt}[_dve_exact_value(companions[(:utility, uid,
                                                                        Tuple(I) .- 1)],
                                                            context, Tuple(I) .- 1)
                                           for I in CartesianIndices(table)] : table
            run_inputs[(:utility, utility_name(id, uid))] = Factor(collect(FiniteAxis,
                                                                           utility_axes),
                                                                   exact_table)
        end
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
    version = backend === nothing ? 1 : 2
    # Insertion order is the schema's property order, so `JSON3.write` emits the keys in
    # that order whatever the Julia version's string hashing; every nested object is a
    # named tuple, whose fields follow the schema too.
    certificate = OrderedDict{String,Any}("format" => "ecorecipes.dve-certificate",
                                          "version" => version,
                                          "provenance" => (implementation_manifest_sha256=_DVE_CERTIFICATE_SOURCE,
                                                           model_name=String(model_name),
                                                           exporter="InfluenceDiagrams.jl/$(pkgversion(@__MODULE__))/export_dve_certificate-v$(version)",
                                                           origin="runtime",
                                                           exact_source=numeric_mode ==
                                                                        :binary64_exact ?
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
                                          "topological_order" => [_dve_source_id(v, owner)
                                                                  for v in order],
                                          "decision_order" => [_dve_source_id(d, owner)
                                                               for d in ds],
                                          "mechanisms" => mechs, "decisions" => decs,
                                          "precedence" => prec,
                                          "utilities" => us,
                                          "evidence" => (hard=hard, likelihood=nothing))
    backend === nothing && return certificate
    certificate["solution"] = _dve_solution(snapshot, backend, data, run_inputs,
                                            normalization_tol, owner)
    return certificate
end
