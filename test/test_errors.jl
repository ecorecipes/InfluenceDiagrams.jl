# The exception contract of ADR 0013. Every exception type BayesianNetworks and
# BayesianNetworkInference export is re-exported here as its owner's binding, and the three
# names that frozen checkers compare (`ImpossibleEvidenceError`, `IrregularDiagramError`,
# `ScopeError`) keep their modules and print unqualified where the conformance adapters load
# the packages.
using BayesianNetworkInference: BayesianNetworkInference
using BayesianNetworkFormats: BayesianNetworkFormats

function exported_exception_names(M)
    return filter(names(M)) do n
        T = getglobal(M, n)
        return T isa Type && T <: Exception
    end
end

@testset "errors" begin
    @testset "hierarchy" begin
        @test InfluenceDiagramError <: BayesNetError
        @test InfluenceDiagramError <: AnyBayesNetError
        @test parentmodule(IrregularDiagramError) === InfluenceDiagrams
    end

    @testset "re-exports" begin
        exported = names(InfluenceDiagrams)
        for M in (BayesianNetworks, BayesianNetworkInference),
            n in exported_exception_names(M)

            @test n in exported
            @test getglobal(InfluenceDiagrams, n) === getglobal(M, n)
        end
        @test issubset([:ImpossibleEvidenceError, :ScopeError, :InferenceError,
                        :FiniteKernelsError, :BayesianNetworkFormatsError,
                        :AnyBayesNetError],
                       exported)
        # Formats' root only, never its concrete types.
        for n in exported_exception_names(BayesianNetworkFormats)
            n === :BayesianNetworkFormatsError && continue
            @test n ∉ exported
        end
    end

    @testset "frozen names" begin
        adapter = Module(:AdapterLike)
        Core.eval(adapter,
                  :(using BayesianNetworks, BayesianNetworkInference, InfluenceDiagrams))
        shown(T) = sprint(show, T; context=:module => adapter)
        for (T, M) in ((ImpossibleEvidenceError, BayesianNetworks),
                       (IrregularDiagramError, InfluenceDiagrams),
                       (ScopeError, BayesianNetworkInference))
            @test parentmodule(T) === M
            @test string(T) == string(nameof(T))
            @test shown(T) == string(nameof(T))
        end
    end

    @testset "a trace-budget ScopeError is a BayesNetError" begin
        e = try
            trace_decision_elimination(umbrella_model(); max_entries=1)
        catch err
            err
        end
        @test e isa ScopeError
        @test e isa BayesNetError && e isa AnyBayesNetError
    end
end
