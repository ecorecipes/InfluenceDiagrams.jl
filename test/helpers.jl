using Random
using JSON3
using Graphs: nv, ne
using BayesianNetworks: BayesianNetworks
using BayesianNetworkFormats: BayesianNetworkFormats
using BayesianNetworkInference: BayesianNetworkInference
using BayesianNetworks: BayesNetError, MissingMechanismError, DuplicateGeneratorError,
                        DanglingReferenceError, PositionError, DuplicateNameError,
                        CyclicBayesNetError, UnknownStateError, UnknownVariableError,
                        MissingKernelError, ImpossibleEvidenceError

# A random tiny influence diagram with no-forgetting: chance variables (2 or 3
# states) and decisions (2 actions) are placed in a random total order; mechanisms and
# information sets read earlier variables only, so the diagram is regular; every later
# decision observes everything an earlier one did plus the earlier action. Information
# sets are kept small (`max_info_states` joint states) so that exhaustive search stays
# cheap.
function random_influence_diagram(rng::AbstractRNG; nchance=rand(rng, 2:4),
                                  ndecision=rand(rng, 1:2), nutility=rand(rng, 1:2),
                                  max_parents=2, max_scope=2, max_info_states=6,
                                  max_actions=2, max_chance_states=3)
    chance = [Symbol("C", i) for i in 1:nchance]
    dec = [Symbol("D", i) for i in 1:ndecision]
    order = shuffle(rng, vcat(chance, dec))
    # decisions keep their index order
    dpos = sort([findfirst(==(d), order) for d in dec])
    for (i, d) in enumerate(dec)
        order[dpos[i]] = d
    end
    # `max_actions` and `max_chance_states` keep the defaults that every caller of this
    # generator was written against: the exhaustive oracle costs |A_D|^|info states| per
    # decision, so raising them without also lowering `max_info_states` makes it
    # intractable. The DVE oracle comparison widens them deliberately, because with every
    # decision binary a permutation of the action axis is undetectable.
    nst = Dict(v => (v in dec ? rand(rng, 2:max_actions) : rand(rng, 2:max_chance_states))
               for v in order)
    vars = [v => [Symbol(v, "_", j) for j in 1:nst[v]] for v in order]
    mechanisms = Pair{Symbol,Any}[]
    decisions = Pair{Symbol,Any}[]
    previous_info = Symbol[]
    for (i, v) in enumerate(order)
        earlier = order[1:(i - 1)]
        if v in chance
            k = min(length(earlier), rand(rng, 0:max_parents))
            ps = shuffle(rng, earlier)[1:k]
            push!(mechanisms, v => ps)
        else
            info = copy(previous_info)
            budget = prod(Int[nst[x] for x in info]; init=1)
            for x in shuffle(rng, setdiff(earlier, previous_info))
                rand(rng) < 0.6 || continue
                budget * nst[x] <= max_info_states || continue
                push!(info, x)
                budget *= nst[x]
            end
            push!(decisions, v => info)
            previous_info = vcat(info, [v])
        end
    end
    utilities = Pair{Symbol,Any}[]
    for j in 1:nutility
        k = rand(rng, 1:min(max_scope, length(order)))
        push!(utilities, Symbol("U", j) => shuffle(rng, order)[1:k])
    end
    return influence_diagram(vars...; mechanisms=mechanisms, decisions=decisions,
                             utilities=utilities)
end

function random_influence_model(rng::AbstractRNG; kw...)
    id = random_influence_diagram(rng; kw...)
    m = InfluenceDiagramModel(id)
    for x in chance_names(id)
        m = bind_kernel(m, x => random_kernel(rng, parent_space(m, x), space(m, x)))
    end
    for u in utility_names(id)
        dims = Tuple(nstates(id, v) for v in utility_scope(id, u))
        m = bind_utility(m, u => 20 .* rand(rng, dims...) .- 10)
    end
    return m
end

# Whether two strategies choose the same action on every information state of every
# decision that has positive probability under the first strategy.
function agree_on_reachable(m::InfluenceDiagramModel, σ1::Strategy, σ2::Strategy;
                            atol=1e-12)
    id = syntax(m)
    bn = instantiate(m, σ1)
    J = joint_table(bn)
    for d in decisions(id)
        name = decision_name(id, d)
        info = information_names(id, d)
        p1, p2 = σ1[name], σ2[name]
        if isempty(info)
            p1() == p2() || return false
            continue
        end
        P = marginal(bn, info)
        for ci in CartesianIndices(size(P.codom))
            P.table[ci] > atol || continue
            labels = ntuple(i -> P.codom.axes[i].labels[ci[i]], length(info))
            p1(labels...) == p2(labels...) || return false
        end
    end
    return true
end
