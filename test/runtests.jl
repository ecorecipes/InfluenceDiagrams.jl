using Test
using InfluenceDiagrams

include("helpers.jl")

@testset "InfluenceDiagrams" begin
    include("test_schema.jl")
    include("test_construction.jl")
    include("test_validation.jl")
    include("test_policies.jl")
    include("test_model.jl")
    include("test_instantiate.jl")
    include("test_expected_utility.jl")
    include("test_stable_utility.jl")
    include("test_valuation.jl")
    include("test_optimize.jl")
    include("test_limited_memory.jl")
    include("test_information.jl")
    include("test_formats.jl")
    include("test_graphics.jl")
    include("test_serialization.jl")
    include("test_regressions.jl")
    include("test_certificates.jl")
end
