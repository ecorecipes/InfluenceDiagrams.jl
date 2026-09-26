ENV["GKSwstype"] = get(ENV, "GKSwstype", "100")

using Documenter
using DocumenterCitations
using InfluenceDiagrams

DocMeta.setdocmeta!(InfluenceDiagrams, :DocTestSetup, :(using InfluenceDiagrams);
                    recursive=true)

# Tutorials are rendered quarto vignettes copied into docs/src/tutorials by
# scripts/sync_vignettes.jl. The page list is built from the files on disk so
# it never has to be maintained by hand.
function tutorial_pages()
    dir = joinpath(@__DIR__, "src", "tutorials")
    isdir(dir) || return Pair{String,String}[]
    files = sort(filter(f -> endswith(f, ".md"), readdir(dir)))
    map(files) do f
        title = f
        for line in eachline(joinpath(dir, f))
            m = match(r"^#\s+(.*)", line)
            if m !== nothing
                title = String(strip(m.captures[1]))
                break
            end
        end
        return title => "tutorials/" * f
    end
end

# The bibliography is the shared workspace `docs/references.bib`, copied into
# docs/src by scripts/sync_references.jl.
bib = CitationBibliography(joinpath(@__DIR__, "src", "references.bib");
                           style=:authoryear)

pages = Any["Home" => "index.md", "API Reference" => "api.md",
            "Algorithm guarantees" => "algorithm_contract.md",
            "Model certificates" => "certificates.md",
            "References" => "references.md"]
tutorials = tutorial_pages()
isempty(tutorials) || push!(pages, "Tutorials" => tutorials)

# Source links need a commit to point at. A checkout without commits (a fresh
# scaffold, a tarball) builds without them instead of failing.
has_commit = success(pipeline(`git -C $(@__DIR__) rev-parse HEAD`; stderr=devnull))
remote_kw = has_commit ? (; repo=Remotes.GitHub("ecorecipes", "InfluenceDiagrams.jl")) :
            (; remotes=nothing)

makedocs(;
         remote_kw...,
         modules=[InfluenceDiagrams],
         sitename="InfluenceDiagrams.jl",
         authors="Simon Frost",
         format=Documenter.HTML(;
                                prettyurls=get(ENV, "CI", "false") == "true",
                                canonical="https://ecorecipes.github.io/InfluenceDiagrams.jl",
                                repolink="https://github.com/ecorecipes/InfluenceDiagrams.jl",
                                edit_link="main",
                                # The generated API reference exceeds Documenter's page-size
                                # warning threshold; it is a reference page, not an example.
                                size_threshold_ignore=["api.md"]),
         plugins=[bib],
         pages=pages)

"--no-deploy" in ARGS || deploydocs(;
                                    repo="github.com/ecorecipes/InfluenceDiagrams.jl.git",
                                    devbranch="main")
