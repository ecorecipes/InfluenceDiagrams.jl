mutable struct _DVETraceRecorder
    data::Dict{String,Any}
    remaining::Int
    compilation::Bool
end

function _DVETraceRecorder(data::Dict{String,Any}, remaining::Int)
    return _DVETraceRecorder(data, remaining, false)
end

function _trace_rational(value::Rational{BigInt}, owner)
    ndigits(abs(numerator(value))) <= 4096 && ndigits(denominator(value)) <= 4096 ||
        throw(UtilityScopeError(owner, :value,
                                "trace rationals with at most 4096 decimal digits", value))
    return Dict("numerator" => string(numerator(value)),
                "denominator" => string(denominator(value)))
end

function _trace_dve_factor!(recorder, factor::Factor{Rational{BigInt}})
    length(factor) <= recorder.remaining ||
        throw(BayesianNetworkInference.ScopeError(:trace_decision_elimination,
                                                  "the trace cell budget was exceeded",
                                                  copy(factor.vars)))
    recorder.remaining -= length(factor)
    return Dict{String,Any}("scope" => String.(factor.vars),
                            "values" => [_trace_rational(value, :trace)
                                         for value in vec(factor.table)])
end

function _trace_valuation!(recorder, value)
    return Dict("probability" => _trace_dve_factor!(recorder, value.φ),
                "utility" => _trace_dve_factor!(recorder, value.ψ))
end

function _trace_binary64_table!(recorder, kind, name, table)
    eltype(table) == Float64 ||
        throw(DVEExportError(:compilation_scalar_type, Symbol(kind), nothing, String(name),
                             Int[], "compilation capture requires Float64 source tables"))
    all(isfinite, table) ||
        throw(DVEExportError(:nonfinite_compilation_value, Symbol(kind), nothing,
                             String(name),
                             Int[], "compilation capture requires finite source values"))
    length(table) <= recorder.remaining ||
        throw(BayesianNetworkInference.ScopeError(:trace_decision_elimination,
                                                  "the trace cell budget was exceeded",
                                                  Symbol[name]))
    recorder.remaining -= length(table)
    return Dict("shape" => Int[size(table)...],
                "values" => [string(reinterpret(UInt64, value); base=16, pad=16)
                             for value in vec(table)])
end

function _trace_compilation!(recorder, input)
    name, kind = input.name, input.kind
    factor = input.compiled
    source = if kind == "chance"
        k = input.source
        2big(length(k.table)) + length(factor.table) <= recorder.remaining ||
            throw(BayesianNetworkInference.ScopeError(:trace_decision_elimination,
                                                      "the compilation cell budget was exceeded",
                                                      Symbol[name]))
        Dict("parents" => String.(input.parents),
             "parent_states" => [String.(labels(axis)) for axis in k.dom.axes],
             "child_states" => String.(labels(only(k.codom.axes))),
             "kernel" => _trace_binary64_table!(recorder, kind, name, k.table),
             "cpt" => _trace_binary64_table!(recorder, kind, name, cpt(k)))
    elseif kind == "utility"
        u = input.source
        u isa TabularUtility ||
            throw(DVEExportError(:unsupported_compilation_source, :utility, nothing,
                                 String(name),
                                 Int[], "compilation capture requires a tabular utility"))
        big(length(u.table)) + length(factor.table) <= recorder.remaining ||
            throw(BayesianNetworkInference.ScopeError(:trace_decision_elimination,
                                                      "the compilation cell budget was exceeded",
                                                      Symbol[name]))
        Dict("arguments" => String.(scope(u)),
             "argument_states" => [String.(labels(axis)) for axis in u.scope],
             "table" => _trace_binary64_table!(recorder, kind, name, utility_table(u)))
    else
        throw(DVEExportError(:unsupported_compilation_kind, :input, nothing, String(name),
                             Int[], "unknown compilation input kind"))
    end
    effective = Dict("scope" => String.(factor.vars),
                     "states" => [String.(labels(axis)) for axis in factor.axes],
                     "table" => _trace_binary64_table!(recorder, kind, name, factor.table))
    push!(recorder.data["compilation"]["inputs"],
          Dict("kind" => kind, "name" => String(name), "source" => source,
               "effective" => effective))
    return nothing
end

function (recorder::_DVETraceRecorder)(kind::Symbol, value)
    if kind == :input
        recorder.compilation && _trace_compilation!(recorder, value)
        push!(recorder.data["inputs"],
              Dict{String,Any}("kind" => value.kind, "name" => String(value.name),
                               "parents" => String.(value.parents),
                               "valuation" => _trace_valuation!(recorder, value.value)))
    elseif kind == :conditioned
        recorder.data["conditioned"] = [_trace_valuation!(recorder, item) for item in value]
    elseif kind == :final
        recorder.data["final"] = _trace_valuation!(recorder, value)
    elseif kind == :inactive
        push!(recorder.data["steps"],
              Dict{String,Any}("kind" => "inactive", "variable" => String(value.variable),
                               "inputs" => Int[],
                               "decision" => String(value.decision),
                               "action" => String(value.action)))
    else
        step = Dict{String,Any}("kind" => String(kind),
                                "variable" => String(value.variable),
                                "inputs" => value.inputs .- 1,
                                "combined" => _trace_valuation!(recorder, value.combined),
                                "result" => _trace_valuation!(recorder, value.result))
        if kind == :decision
            step["decision"] = String(value.decision)
            step["policy"] = Dict("scope" => String.(value.policy_scope),
                                  "values" => String.(vec(value.policy)))
        end
        push!(recorder.data["steps"], step)
    end
    return nothing
end

"""
    trace_decision_elimination(model; order=MinFill(), atol=DEFAULT_ATOL,
                               probability_atol=0, max_entries=1_000_000,
                               include_compilation=false)
        -> (solution, trace)

Capture actual exact-rational stable-DVE inputs, conditioned valuations,
combined/reduced buckets and recovered policies using the production driver.
The JSON-compatible `ecorecipes.dve-execution-trace` v1 representation stores
exact rational table entries in first-axis-fastest order and the returned
binary64 value as raw bits. It starts from the effective compiled chance
factors, not a purported proof of CPT compilation.

The default probability-constancy guard is exact for this certificate profile;
accepted rounded diagrams need not satisfy it. A trace is data for an independent
checker, not proof that Julia, its JSON parser or its arithmetic implementation
is verified. `max_entries` bounds captured table cells. Ordinary DVE and stable
DVE defaults are unchanged.

With `include_compilation=true`, emit trace version 2 and also capture the
bound kernel storage, its sanctioned `cpt` conversion, tabular utilities and the
actual Float64 factors consumed by the same production run before rational
conversion. Source CPT/utility and effective-factor arrays are first-axis-fastest;
kernel storage has outputs before inputs. These copied source tables share
`max_entries` with the ordinary trace. This initial compilation profile requires
Float64 kernels and tabular utilities and throws [`DVEExportError`](@ref) for
unsupported sources. It starts at the bound model; linking an original JSON
request to that model is a separate comparison. Version 1 remains the default.
"""
function trace_decision_elimination(m::InfluenceDiagramModel;
                                    order::EliminationStrategy=MinFill(),
                                    atol::Real=BayesianNetworks.DEFAULT_ATOL,
                                    probability_atol::Real=0,
                                    max_entries::Integer=1_000_000,
                                    include_compilation::Bool=false)
    _check_solvable(m; atol)
    _check_probability_tolerance(probability_atol)
    0 < max_entries <= typemax(Int) ||
        throw(ArgumentError("max_entries must be a positive representable integer"))
    id = syntax(m)
    ordered = decision_order(id)
    data = Dict{String,Any}("format" => "ecorecipes.dve-execution-trace",
                            "version" => include_compilation ? 2 : 1,
                            "layout" => "first-axis-fastest",
                            "arithmetic" => "exact-rational-native-v1",
                            "variables" => [Dict("id" => String(name),
                                                 "states" => String.(states(id, name)))
                                            for name in variable_names(id)],
                            "decisions" => [Dict("id" => String(decision_name(id, decision)),
                                                 "variable" => String(variable_name(id,
                                                                                    decision_variable(id,
                                                                                                      decision))),
                                                 "information" => String.(information_names(id,
                                                                                            decision)))
                                            for decision in ordered],
                            "evidence" => Dict(String(name) => String(value)
                                               for (name, value) in evidence(m)),
                            "inputs" => Any[], "steps" => Any[],
                            "metadata" => Dict("producer" => "InfluenceDiagrams.trace_decision_elimination",
                                               "runtime_version" => string(VERSION),
                                               "package_version" => string(Base.pkgversion(@__MODULE__))))
    if include_compilation
        data["compilation"] = Dict{String,Any}("format" => "ecorecipes.dve-compilation",
                                               "version" => 1,
                                               "scalar" => "binary64",
                                               "table_layout" => "first-axis-fastest",
                                               "kernel_layout" => "outputs-first",
                                               "inputs" => Any[])
    end
    recorder = _DVETraceRecorder(data, Int(max_entries), include_compilation)
    solution = _decision_elimination(m, order, probability_atol, Rational{BigInt}, recorder)
    data["policies"] = [Dict("decision" => String(decision_name(id, decision)),
                             "scope" => String.(information_names(id, decision)),
                             "values" => String.(vec(policy_table(solution.strategy[decision_name(id,
                                                                                                  decision)]))))
                        for decision in ordered]
    data["result"] = string(reinterpret(UInt64, solution.expected_utility); base=16, pad=16)
    return solution, data
end
