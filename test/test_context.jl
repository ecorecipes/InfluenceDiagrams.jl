# External decision contexts. The oracle is the augmented closed diagram: with a product
# prior, giving each exogenous variable a root mechanism with its marginal and adding the
# terminal as an ordinary utility node must give the same expected utilities and optima.
# A joint (non-product) prior is checked against a brute-force sum over joint states written
# here, independently of the package's instantiation.

# The model with the mechanisms of the root chance variables `xs` removed: they become
# exogenous. The removed kernels stay bound but unused.
function cut_roots(m::InfluenceDiagramModel, xs::Vector{Symbol})
    syn = deepcopy(syntax(m))
    for x in xs
        mech = mechanism_of(syn, variable_id(syn, x))
        isempty(inputs(syn, mech)) || error("$x is not a root")
        cascading_rem_part!(syn, :Mechanism, mech)
    end
    bm = BayesModel(syn; spaces=spaces(m), kernels=kernels(m))
    return InfluenceDiagramModel(bm; utilities=bound_utilities(m))
end

# The root marginals of `xs` in `m` as a product table, axis i over xs[i].
function product_prior(m::InfluenceDiagramModel, xs::Vector{Symbol})
    margs = [vec(kernel(m, x).table) for x in xs]
    table = ones(Tuple(length.(margs)))
    for ci in CartesianIndices(table)
        table[ci] = prod(margs[i][ci[i]] for i in eachindex(xs); init=1.0)
    end
    return table
end

# `m` with a utility node `name` over `vars` (no repeats) bound to `table`.
function add_terminal_node(m::InfluenceDiagramModel, name::Symbol, vars::Vector{Symbol},
                           table)
    syn = deepcopy(syntax(m))
    add_utility!(syn, name; scope=vars)
    out = InfluenceDiagramModel(BayesModel(m.model; syntax=syn);
                                utilities=bound_utilities(m))
    return bind_utility(out, name => table)
end

# The contextual value by brute force over every joint state of every variable:
# Σ_x μ(x_exo) Π chance kernels(x) Π [σ_D(info) = a_D] (Σ_j u_j(x) + c(x_out)).
function brute_context_value(m::InfluenceDiagramModel, σ::Strategy, prior, terminal)
    id = syntax(m)
    vars = variable_names(id)
    labels = Dict(x => only(space(m, x).axes).labels for x in vars)
    dims = Tuple(length(labels[x]) for x in vars)
    pos = Dict(x => i for (i, x) in enumerate(vars))
    total = 0.0
    for ci in CartesianIndices(dims)
        a = Dict(x => labels[x][ci[pos[x]]] for x in vars)
        w = 1.0
        if prior !== nothing
            pv, μ = prior
            w *= μ[(ci[pos[x]] for x in pv)...]
        end
        for mech in mechanisms(id)
            x = variable_name(id, target(id, mech))
            ps = Symbol[variable_name(id, p) for p in inputs(id, mech)]
            w *= kernel(m, x).table[ci[pos[x]], (ci[pos[p]] for p in ps)...]
        end
        for d in decisions(id)
            name = decision_name(id, d)
            info = information_names(id, d)
            act = variable_name(id, decision_variable(id, d))
            choice = isempty(info) ? σ[name]() : σ[name]((a[x] for x in info)...)
            choice == a[act] || (w = 0.0)
        end
        w == 0 && continue
        u = total_utility(m, a)
        if terminal !== nothing
            tv, c = terminal
            u += c[(ci[pos[x]] for x in tv)...]
        end
        total += w * u
    end
    return total
end

const CONTEXT_BACKENDS = (ExhaustivePolicySearch(),
                          ExhaustivePolicySearch(; brute_force=true),
                          ExhaustivePolicySearch(; stable=true))

# The checks shared by the augmented-oracle comparisons: every strategy's expected utility,
# and every exhaustive backend's optimum, with the context on `cut` equal those on `aug`.
function check_against_augmented(cut, aug, ctx;
                                 strategies=all_deterministic_strategies(aug),
                                 strict_strategy=true)
    for σ in strategies
        @test expected_utility(cut, σ; context=ctx) ≈ expected_utility(aug, σ) atol = 1e-9
        @test expected_utility(cut, σ; context=ctx, stable=true) ≈
              expected_utility(aug, σ; stable=true) atol = 1e-9
    end
    for b in CONTEXT_BACKENDS
        got = optimize(cut, b; context=ctx)
        want = optimize(aug, b)
        @test got.expected_utility ≈ want.expected_utility atol = 1e-9
        @test got.diagnostics.nstrategies == want.diagnostics.nstrategies
        if strict_strategy
            @test got.strategy == want.strategy
        else
            # Near-ties may be broken differently by rounding; the strategy found must still
            # be optimal for the augmented model.
            @test expected_utility(aug, got.strategy) ≈ want.expected_utility atol = 1e-9
        end
    end
end

function umbrella_cut()
    id = influence_diagram(:Weather => [:sunny, :rainy],
                           :Forecast => [:sunny, :cloudy, :rainy],
                           :Umbrella => [:take, :leave];
                           mechanisms=[:Forecast => :Weather],
                           decisions=[:Umbrella => :Forecast],
                           utilities=[:U => (:Weather, :Umbrella)], closed=false)
    m = bind_cpt(InfluenceDiagramModel(id), :Forecast => [0.7 0.2 0.1; 0.15 0.25 0.6])
    return bind_utility(m, :U => [20.0 100.0; 70.0 0.0])
end

# Two correlated exogenous variables, both read by a decision or a utility, and a chance
# variable downstream of one of them. `E` forgets `Y` (limited memory) to keep the number
# of strategies small.
function joint_prior_model()
    id = influence_diagram(:X => [:x1, :x2], :Y => [:y1, :y2, :y3], :Z => [:z1, :z2],
                           :D => [:d1, :d2], :E => [:e1, :e2];
                           mechanisms=[:Z => (:X, :D)],
                           decisions=[:D => :Y, :E => (:D, :Z)],
                           utilities=[:U1 => (:X, :D), :U2 => (:Z, :E, :Y)], closed=false)
    m = InfluenceDiagramModel(id)
    zt = zeros(2, 2, 2)   # (X, D, Z)
    zt[1, 1, :] = [0.9, 0.1]
    zt[1, 2, :] = [0.4, 0.6]
    zt[2, 1, :] = [0.2, 0.8]
    zt[2, 2, :] = [0.5, 0.5]
    m = bind_cpt(m, :Z => zt)
    return bind_utility(m,
                        [:U1 => [10.0 -5.0; -20.0 15.0],
                         :U2 => reshape(collect(-6.0:5.0), 2, 2, 3)])
end

@testset "decision contexts" begin
    @testset "umbrella with Weather exogenous" begin
        cut = umbrella_cut()
        @test_throws MissingMechanismError optimize(cut, ExhaustivePolicySearch())
        prior = [:Weather] => [0.7, 0.3]
        ctx = DecisionContext(; prior=prior)
        check_against_augmented(cut, umbrella_model(), ctx)
        @test optimize(cut, ExhaustivePolicySearch(); context=ctx).expected_utility ≈ 77
        # A terminal over the exogenous variable, and over the action.
        for tv in ([:Weather], [:Umbrella], [:Forecast, :Umbrella])
            dims = Tuple(nstates(syntax(cut), x) for x in tv)
            c = reshape(collect(1.0:prod(dims)), dims) .* 3 .- 7
            aug = add_terminal_node(umbrella_model(), :T, tv, c)
            check_against_augmented(cut, aug,
                                    DecisionContext(; prior=prior, terminal=tv => c))
        end
        @test optimize(cut, ExhaustivePolicySearch();
                       context=DecisionContext(; prior=prior,
                                               terminal=[:Weather] => [5.0, -3.0])).expected_utility ≈
              77 + 0.7 * 5 - 0.3 * 3
    end

    @testset "two-stage with Oil exogenous" begin
        full = two_stage_model()
        cut = cut_roots(full, [:Oil])
        @test_throws MissingMechanismError expected_utility(cut,
                                                            first(all_deterministic_strategies(cut)))
        ctx = DecisionContext(; prior=[:Oil] => product_prior(full, [:Oil]))
        check_against_augmented(cut, full, ctx)
        @test optimize(cut, ExhaustivePolicySearch(); context=ctx).expected_utility ≈ 21
        c = [1.0 -2.0; 4.0 0.5]   # (Oil, Drill)
        check_against_augmented(cut, add_terminal_node(full, :T, [:Oil, :Drill], c),
                                DecisionContext(; prior=[:Oil] => [0.5, 0.5],
                                                terminal=[:Oil, :Drill] => c))
    end

    @testset "random diagrams, product prior" begin
        rng = MersenneTwister(20261017)
        ncases = 0
        for trial in 1:40
            full = random_influence_model(rng)
            id = syntax(full)
            roots = Symbol[x
                           for x in chance_names(id)
                           if isempty(inputs(id, mechanism_of(id, variable_id(id, x))))]
            isempty(roots) && continue
            n_deterministic_strategies(full) <= 256 || continue
            xs = shuffle(rng, roots)[1:rand(rng, 1:length(roots))]
            cut = cut_roots(full, xs)
            vars = variable_names(id)
            tv = vars[rand(rng, 1:length(vars), rand(rng, 1:2))]
            tv = unique(tv)
            c = 10 .* randn(rng, Tuple(nstates(id, x) for x in tv))
            aug = add_terminal_node(full, :T, tv, c)
            ctx = DecisionContext(; prior=xs => product_prior(full, xs), terminal=tv => c)
            σs = collect(all_deterministic_strategies(full))
            sample = σs[unique(rand(rng, 1:length(σs), 6))]
            check_against_augmented(cut, aug, ctx; strategies=sample, strict_strategy=false)
            ncases += 1
        end
        @test ncases >= 10
    end

    @testset "joint prior against a brute-force sum" begin
        m = joint_prior_model()
        μ = [0.10 0.25 0.05; 0.30 0.0 0.30]   # (X, Y), not a product
        c = reshape(collect(1.0:8.0), 2, 2, 2) .- 4   # (Z, E, Z): read on the diagonal
        ctx = DecisionContext(; prior=[:X, :Y] => μ, terminal=[:Z, :E, :Z] => c)
        # The prior listed in the other order is the same context.
        ctx_t = DecisionContext(; prior=[:Y, :X] => permutedims(μ),
                                terminal=[:Z, :E, :Z] => c)
        values = Float64[]
        for σ in all_deterministic_strategies(m)
            want = brute_context_value(m, σ, ctx.prior, ctx.terminal)
            push!(values, want)
            @test expected_utility(m, σ; context=ctx) ≈ want atol = 1e-12
            @test expected_utility(m, σ; context=ctx_t) ≈ want atol = 1e-12
            @test expected_utility(m, σ; context=ctx, stable=true) ≈ want atol = 1e-12
        end
        best = maximum(values)
        first_best = findfirst(v -> v >= best - 1e-12, values)
        σbest = collect(all_deterministic_strategies(m))[first_best]
        for b in CONTEXT_BACKENDS, cx in (ctx, ctx_t)
            sol = optimize(m, b; context=cx)
            @test sol.expected_utility ≈ best atol = 1e-12
            @test sol.strategy == σbest
        end
        # Random joint priors and terminals on random diagrams, all roots cut.
        rng = MersenneTwister(17)
        ncases = 0
        for trial in 1:40
            full = random_influence_model(rng)
            id = syntax(full)
            roots = Symbol[x
                           for x in chance_names(id)
                           if isempty(inputs(id, mechanism_of(id, variable_id(id, x))))]
            length(roots) >= 2 || continue
            n_deterministic_strategies(full) <= 32 || continue
            ncases >= 8 && break
            cut = cut_roots(full, roots)
            μr = rand(rng, Tuple(nstates(id, x) for x in roots)...)
            μr[rand(rng, eachindex(μr))] = 0.0
            μr ./= sum(μr)
            vars = variable_names(id)
            tv = vars[rand(rng, 1:length(vars), 3)]   # repeats allowed
            cr = 10 .* randn(rng, Tuple(nstates(id, x) for x in tv))
            rctx = DecisionContext(; prior=roots => μr, terminal=tv => cr)
            σs = collect(all_deterministic_strategies(cut))
            vals = [brute_context_value(cut, σ, rctx.prior, rctx.terminal) for σ in σs]
            for i in unique(rand(rng, eachindex(σs), 4))
                @test expected_utility(cut, σs[i]; context=rctx) ≈ vals[i] atol = 1e-9
            end
            # The per-strategy backends evaluate every strategy on every prior state.
            backends = length(σs) <= 8 ? CONTEXT_BACKENDS : CONTEXT_BACKENDS[1:1]
            for b in backends
                sol = optimize(cut, b; context=rctx)
                @test sol.expected_utility ≈ maximum(vals) atol = 1e-9
                @test brute_context_value(cut, sol.strategy, rctx.prior, rctx.terminal) ≈
                      maximum(vals) atol = 1e-9
            end
            ncases += 1
        end
        @test ncases >= 5
    end

    @testset "repeated terminal variables read the diagonal" begin
        cut = umbrella_cut()
        prior = [:Weather] => [0.7, 0.3]
        rep = DecisionContext(; prior=prior,
                              terminal=[:Umbrella, :Umbrella] => [1.0 100.0; -100.0 2.0])
        diag = DecisionContext(; prior=prior, terminal=[:Umbrella] => [1.0, 2.0])
        for σ in all_deterministic_strategies(cut)
            @test expected_utility(cut, σ; context=rep) ==
                  expected_utility(cut, σ; context=diag)
        end
        for b in CONTEXT_BACKENDS
            @test optimize(cut, b; context=rep).expected_utility ==
                  optimize(cut, b; context=diag).expected_utility
        end
    end

    @testset "an empty context is no context" begin
        m = umbrella_model()
        ev = observe(m, :Forecast => :rainy)
        for σ in all_deterministic_strategies(m)
            @test expected_utility(m, σ; context=DecisionContext()) ===
                  expected_utility(m, σ)
            @test expected_utility(ev, σ; context=DecisionContext()) ===
                  expected_utility(ev, σ)
        end
        for mm in (m, ev, two_stage_model()),
            b in (CONTEXT_BACKENDS..., DecisionVariableElimination())

            got = optimize(mm, b; context=DecisionContext())
            want = optimize(mm, b)
            @test got.expected_utility === want.expected_utility
            @test got.strategy == want.strategy
            @test got.diagnostics == want.diagnostics
        end
        @test optimize(m; context=DecisionContext()).expected_utility ≈ 77
        # A prior over no variables, on a closed model, weighs every state by one.
        ctx = DecisionContext(; prior=Symbol[] => fill(1.0))
        @test optimize(m, ExhaustivePolicySearch(); context=ctx).expected_utility ≈ 77
        @test expected_utility(m, :Umbrella => :take; context=ctx) ==
              expected_utility(m, :Umbrella => :take)
        # A terminal over no variables adds a constant.
        ctx = DecisionContext(; terminal=Symbol[] => fill(2.5))
        @test optimize(m, ExhaustivePolicySearch(); context=ctx).expected_utility ≈ 79.5
        @test expected_utility(m, :Umbrella => :take; context=ctx) ≈ 37.5
    end

    @testset "malformed contexts" begin
        @test_throws ArgumentError DecisionContext(; prior=[0.5, 0.5])
        @test_throws ArgumentError DecisionContext(; prior=[:A] => [0.5 0.5])
        @test_throws ArgumentError DecisionContext(; prior=["A"] => [0.5, 0.5])
        @test_throws ArgumentError DecisionContext(; prior=[:A] => [:x, :y])
        @test_throws ArgumentError DecisionContext(; prior=[:A, :A] => [0.5 0.0; 0.0 0.5])
        @test_throws ArgumentError DecisionContext(; prior=[:A] => [1.5, -0.5])
        @test_throws ArgumentError DecisionContext(; prior=[:A] => [NaN, 1.0])
        @test_throws ArgumentError DecisionContext(; terminal=[:A] => [Inf, 1.0])
        @test_throws ArgumentError DecisionContext(; terminal=[:A, :B] => [1.0, 2.0])
        # Signed and repeated terminals are fine.
        @test DecisionContext(; terminal=[:A, :A] => [-1.0 2.0; 3.0 -4.0]) isa
              DecisionContext
        @test sprint(show,
                     DecisionContext(; prior=[:A] => [1.0], terminal=[:B] => [0.0])) ==
              "DecisionContext(prior over [:A], terminal over [:B])"
        # The input array is copied.
        μ = [0.7, 0.3]
        ctx = DecisionContext(; prior=[:Weather] => μ)
        μ[1] = 0.0
        @test last(ctx.prior) == [0.7, 0.3]
    end

    @testset "contexts checked against the model" begin
        cut = umbrella_cut()
        σ = first(all_deterministic_strategies(cut))
        check(ctx) = (expected_utility(cut, σ; context=ctx),
                      optimize(cut, ExhaustivePolicySearch(); context=ctx))
        for f in (ctx -> expected_utility(cut, σ; context=ctx),
                  ctx -> optimize(cut, ExhaustivePolicySearch(); context=ctx),
                  ctx -> optimize(cut, ExhaustivePolicySearch(; brute_force=true);
                                  context=ctx))
            # Unknown variables.
            @test_throws UnknownVariableError f(DecisionContext(;
                                                                prior=[:Rain] => [0.5, 0.5]))
            @test_throws UnknownVariableError f(DecisionContext(;
                                                                prior=[:Weather] => [0.7,
                                                                                     0.3],
                                                                terminal=[:Rain] => [1.0]))
            # Wrong state counts.
            e = try
                f(DecisionContext(; prior=[:Weather] => [0.5, 0.25, 0.25]))
            catch err
                err
            end
            @test e isa ContextStateCountError && e.part == :prior &&
                  e.variable == :Weather && e.expected == 2 && e.got == 3
            @test occursin("Weather", sprint(showerror, e))
            e = try
                f(DecisionContext(; prior=[:Weather] => [0.7, 0.3],
                                  terminal=[:Umbrella, :Forecast] => zeros(2, 2)))
            catch err
                err
            end
            @test e isa ContextStateCountError && e.part == :terminal &&
                  e.variable == :Forecast
            # Coverage: the exogenous variable left out, or a non-exogenous one listed.
            e = try
                f(DecisionContext(; terminal=[:Weather] => [1.0, 2.0]))
            catch err
                err
            end
            @test e isa ExogenousCoverageError && e.uncovered == [:Weather] &&
                  isempty(e.not_exogenous)
            @test occursin("Weather", sprint(showerror, e))
            e = try
                f(DecisionContext(; prior=[:Weather, :Forecast] => fill(1 / 6, 2, 3)))
            catch err
                err
            end
            @test e isa ExogenousCoverageError && isempty(e.uncovered) &&
                  e.not_exogenous == [:Forecast]
            @test occursin("Forecast", sprint(showerror, e))
            e = try
                f(DecisionContext(; prior=[:Weather, :Umbrella] => fill(0.25, 2, 2)))
            catch err
                err
            end
            @test e isa ExogenousCoverageError && e.not_exogenous == [:Umbrella]
            # A prior that does not sum to one.
            @test_throws ArgumentError f(DecisionContext(; prior=[:Weather] => [0.7, 0.2]))
        end
        # The normalisation tolerance is the solver's atol.
        loose = DecisionContext(; prior=[:Weather] => [0.7, 0.3 + 1e-7])
        @test_throws ArgumentError optimize(cut, ExhaustivePolicySearch(); context=loose)
        @test optimize(cut, ExhaustivePolicySearch(); context=loose,
                       atol=1e-6).expected_utility ≈
              77 atol = 1e-4
        # Accepted, the prior is used as given, not renormalised: the value tables agree with
        # the reference decomposition to rounding, well inside the 1e-7 a renormalisation
        # would move the value by.
        for prior in ([0.7, 0.3 + 1e-7], [0.7 - 4e-7, 0.3])
            ctx = DecisionContext(; prior=[:Weather] => prior,
                                  terminal=[:Umbrella] => [-2.0, 3.0])
            fast = optimize(cut, ExhaustivePolicySearch(); context=ctx, atol=1e-6)
            slow = optimize(cut, ExhaustivePolicySearch(; brute_force=true); context=ctx,
                            atol=1e-6)
            @test fast.diagnostics.method == :value_table
            @test fast.strategy == slow.strategy
            @test isapprox(fast.expected_utility, slow.expected_utility; rtol=1e-14)
            @test isapprox(fast.expected_utility,
                           expected_utility(cut, fast.strategy; context=ctx, atol=1e-6);
                           rtol=1e-14)
        end
        # A prior on a closed model covers variables that have mechanisms.
        @test_throws ExogenousCoverageError optimize(umbrella_model(),
                                                     ExhaustivePolicySearch();
                                                     context=DecisionContext(;
                                                                             prior=[:Weather] => [0.7,
                                                                                                  0.3]))
        @test ExogenousCoverageError <: InfluenceDiagramError
        @test ContextStateCountError <: InfluenceDiagramError
    end

    @testset "refusals: decision variable elimination and evidence" begin
        cut = umbrella_cut()
        ctx = DecisionContext(; prior=[:Weather] => [0.7, 0.3])
        for f in (() -> optimize(cut, DecisionVariableElimination(); context=ctx),
                  () -> optimize(cut; context=ctx),
                  () -> optimize(umbrella_model(), DecisionVariableElimination();
                                 context=DecisionContext(; terminal=[:Weather] => [1.0, 0.0])))
            e = try
                f()
            catch err
                err
            end
            @test e isa ArgumentError
            @test occursin("ExhaustivePolicySearch", sprint(showerror, e))
        end
        ev = observe(cut, :Forecast => :rainy)
        σ = first(all_deterministic_strategies(cut))
        @test_throws ArgumentError expected_utility(ev, σ; context=ctx)
        for b in CONTEXT_BACKENDS
            e = try
                optimize(ev, b; context=ctx)
            catch err
                err
            end
            @test e isa ArgumentError && occursin("evidence", sprint(showerror, e))
        end
        # Without a context, evidence keeps working as before.
        @test optimize(observe(umbrella_model(), :Forecast => :rainy),
                       ExhaustivePolicySearch()).expected_utility ≈
              optimize(observe(umbrella_model(), :Forecast => :rainy)).expected_utility
    end
end
