# Every exported name this package owns has a docstring (CLAUDE.md, "Style"). A name
# re-exported from another package is that package's to document, so it is skipped.
# `Base.which` names the module that owns a binding; `parentmodule` would throw on
# constants and `Union`s.
function owned_undocumented(M; allow=Symbol[])
    return filter(n -> Base.which(M, n) === M && n ∉ allow, Base.Docs.undocumented_names(M))
end

@testset "docstrings on every exported name" begin
    @test isempty(owned_undocumented(InfluenceDiagrams))
end

@testset "decision_elimination documents its default constancy tolerance" begin
    # Review finding 6: the signature said `atol = 1e-9`, the default before `nothing`, which
    # follows `normalization_atol`.
    doc = string(@doc InfluenceDiagrams.decision_elimination)
    @test occursin("atol = nothing", doc) && !occursin("atol = 1e-9", doc)
end
