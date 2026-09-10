function _rational_exponent(n::BigInt, d::BigInt)
    exponent = ndigits(n; base=2) - ndigits(d; base=2)
    below = exponent >= 0 ? n < (d << exponent) : (n << -exponent) < d
    return below ? exponent - 1 : exponent
end

# Integer rounding and word construction avoid ambient BigFloat precision,
# floating-point scaling and double rounding at representation boundaries.
function _nearest_binary64(value::Rational{BigInt})
    iszero(value) && return 0.0
    sign_bits = value < 0 ? 0x8000000000000000 : UInt64(0)
    n, d = abs(numerator(value)), denominator(value)
    exponent = _rational_exponent(n, d)
    exponent > 1023 && return reinterpret(Float64, sign_bits | 0x7ff0000000000000)
    exponent < -1075 && return reinterpret(Float64, sign_bits)
    shift = max(exponent - 52, -1074)
    numerator_ = shift < 0 ? n << -shift : n
    denominator_ = shift > 0 ? d << shift : d
    mantissa, remainder = divrem(numerator_, denominator_)
    twice = 2remainder
    if twice > denominator_ || (twice == denominator_ && isodd(mantissa))
        mantissa += 1
    end
    hidden_bit = big(1) << 52
    if mantissa < hidden_bit
        word = UInt64(mantissa)
    else
        field = max(exponent, -1022) + 1023
        if mantissa == 2hidden_bit
            mantissa = hidden_bit
            field += 1
        end
        word = (UInt64(field) << 52) | UInt64(mantissa - hidden_bit)
    end
    return reinterpret(Float64, sign_bits | word)
end

function _rational_log(value::Rational{BigInt})
    iszero(value) && return -Inf
    n, d = numerator(value), denominator(value)
    exponent = _rational_exponent(n, d)
    mantissa = exponent >= 0 ? n // (d << exponent) : (n << -exponent) // d
    return log(_nearest_binary64(mantissa)) + exponent * log(2.0)
end
