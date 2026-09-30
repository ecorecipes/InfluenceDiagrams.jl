# Correct rounding and the binary exponent of an exact rational live in BayesianNetworks
# (`exact_rounding.jl`, ADR 0016), shared with its exact evaluator fallback and with
# BayesianNetworkInference's dyadic arithmetic. They are imported here, so
# `InfluenceDiagrams._nearest_binary64` is still that one definition.
using BayesianNetworks: _nearest_binary64, _rational_exponent

function _rational_log(value::Rational{BigInt})
    iszero(value) && return -Inf
    n, d = numerator(value), denominator(value)
    exponent = _rational_exponent(n, d)
    mantissa = exponent >= 0 ? n // (d << exponent) : (n << -exponent) // d
    return log(_nearest_binary64(mantissa)) + exponent * log(2.0)
end
