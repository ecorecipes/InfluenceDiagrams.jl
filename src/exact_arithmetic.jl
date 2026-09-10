function _rational_exponent(n::BigInt, d::BigInt)
    exponent = ndigits(n; base=2) - ndigits(d; base=2)
    below = exponent >= 0 ? n < (d << exponent) : (n << -exponent) < d
    return below ? exponent - 1 : exponent
end

# Integer quotient/remainder rounding avoids the ambient BigFloat precision and
# double rounding at binary64 midpoint, subnormal and overflow boundaries.
function _nearest_binary64(value::Rational{BigInt})
    iszero(value) && return 0.0
    negative = value < 0
    n, d = abs(numerator(value)), denominator(value)
    exponent = _rational_exponent(n, d)
    exponent > 1023 && return negative ? -Inf : Inf
    exponent < -1075 && return negative ? -0.0 : 0.0
    shift = max(exponent - 52, -1074)
    numerator_ = shift < 0 ? n << -shift : n
    denominator_ = shift > 0 ? d << shift : d
    mantissa, remainder = divrem(numerator_, denominator_)
    twice = 2remainder
    if twice > denominator_ || (twice == denominator_ && isodd(mantissa))
        mantissa += 1
    end
    rounded = ldexp(Float64(mantissa), shift)
    return negative ? -rounded : rounded
end

function _rational_log(value::Rational{BigInt})
    iszero(value) && return -Inf
    n, d = numerator(value), denominator(value)
    exponent = _rational_exponent(n, d)
    mantissa = exponent >= 0 ? n // (d << exponent) : (n << -exponent) // d
    return log(_nearest_binary64(mantissa)) + exponent * log(2.0)
end
