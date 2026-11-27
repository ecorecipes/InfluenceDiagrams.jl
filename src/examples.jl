"""
Worked examples: the umbrella problem of Shachter 1986 (cited as `Shachter1986`),
the SPEC §46 reference ecological
influence diagram (matching the `grazing_reference_id` fixtures of
BayesianNetworkFormats.jl), a two-stage test-then-act problem used to exercise
sequential decisions, and two limited-memory problems with published answers: the used
car buyer (Howard 1977) and pig breeding (Lauritzen and Nilsson 2001), with the numbers
of the DecisionProgramming.jl documentation, whose results the tests reproduce.
"""

"""
    umbrella_diagram() -> InfluenceDiagram

The umbrella problem, structure only: chance `Weather` (sunny, rainy) and `Forecast`
(sunny, cloudy, rainy) with `Forecast` depending on `Weather`; decision `Umbrella`
(take, leave) informed by `Forecast`; utility `U` over `(Weather, Umbrella)`.
"""
function umbrella_diagram()
    return influence_diagram(:Weather => [:sunny, :rainy],
                             :Forecast => [:sunny, :cloudy, :rainy],
                             :Umbrella => [:take, :leave];
                             mechanisms=[:Forecast => :Weather],
                             decisions=[:Umbrella => :Forecast],
                             utilities=[:U => (:Weather, :Umbrella)])
end

"""
    umbrella_model() -> InfluenceDiagramModel

[`umbrella_diagram`](@ref) with the numbers of [Shachter1986](@cite):
`P(Weather) = (0.7, 0.3)`,
`P(Forecast | sunny) = (0.7, 0.2, 0.1)`, `P(Forecast | rainy) = (0.15, 0.25, 0.6)`,
`U(sunny, take) = 20`, `U(sunny, leave) = 100`, `U(rainy, take) = 70`,
`U(rainy, leave) = 0`. The maximal expected utility is 70 without information, 77
with the forecast and 91 with the weather observed, so the value of the forecast is 7
and the value of perfect information 21. Matches
`read_influence_diagram(fixture_path("dne/umbrella.dne"))`.
"""
function umbrella_model()
    m = InfluenceDiagramModel(umbrella_diagram())
    m = bind_cpt(m, [:Weather => [0.7, 0.3], :Forecast => [0.7 0.2 0.1; 0.15 0.25 0.6]])
    return bind_utility(m, :U => [20.0 100.0; 70.0 0.0])
end

"""
    reference_grazing_diagram() -> InfluenceDiagram

The reference ecological influence diagram of SPEC §46, structure only:

    Climate -> ClimateForecast, Climate -> SoilMoisture -> Vegetation
    CurrentVegetation -> Vegetation -> HabitatQuality -> Occupancy -> Biodiversity
    GrazingManagement (decision; information: ClimateForecast, CurrentVegetation)
        -> GrazingPressure -> Vegetation
    ConservationBenefit(Biodiversity), ManagementCost(GrazingManagement)

`Vegetation`'s parents are ordered `(SoilMoisture, GrazingPressure, CurrentVegetation)`.
The management decision acts on the vegetation through an uncertain implementation
(`GrazingPressure`), as SPEC §42 recommends.
"""
function reference_grazing_diagram()
    return influence_diagram(:Climate => [:dry, :normal, :wet],
                             :ClimateForecast => [:dry, :normal, :wet],
                             :SoilMoisture => [:low, :medium, :high],
                             :CurrentVegetation => [:sparse, :moderate, :dense],
                             :GrazingManagement => [:exclude, :reduce, :maintain],
                             :GrazingPressure => [:low, :high],
                             :Vegetation => [:sparse, :moderate, :dense],
                             :HabitatQuality => [:poor, :good],
                             :Occupancy => [:absent, :present],
                             :Biodiversity => [:low, :high];
                             mechanisms=[:ClimateForecast => :Climate,
                                         :SoilMoisture => :Climate,
                                         :GrazingPressure => :GrazingManagement,
                                         :Vegetation => (:SoilMoisture, :GrazingPressure,
                                                         :CurrentVegetation),
                                         :HabitatQuality => :Vegetation,
                                         :Occupancy => :HabitatQuality,
                                         :Biodiversity => :Occupancy],
                             decisions=[:GrazingManagement => (:ClimateForecast,
                                                               :CurrentVegetation)],
                             utilities=[:ConservationBenefit => :Biodiversity,
                                        :ManagementCost => :GrazingManagement])
end

"""
    reference_grazing_model() -> InfluenceDiagramModel

[`reference_grazing_diagram`](@ref) with the tables of the `grazing_reference_id`
fixtures of BayesianNetworkFormats.jl bound, so that
`read_influence_diagram(fixture_path("dne/grazing_reference_id.dne")) ≈ reference_grazing_model()`.
Conservation benefit is 0 or 100 for low or high biodiversity; management cost is
-40, -15 or 0 for exclude, reduce or maintain.

With these numbers the diagram is degenerate for the value-of-information analyses of
SPEC §46 (analyses 3 and 4): the maximal expected utility is 36.52, `maintain` is
optimal on every information state, so the optimal policy is constant and every
information set has the same value. Both
`expected_value_of_information(m, :CurrentVegetation, :GrazingManagement)` and
`expected_value_of_perfect_information(m, :GrazingManagement)` are zero (to rounding).
The conservation benefit has to be rescaled (the vignettes multiply it by 10) before
information is worth anything. This is a property of the reference numbers, not of the
algorithms; use [`two_stage_model`](@ref) for a non-degenerate value-of-information
example.
"""
function reference_grazing_model()
    m = InfluenceDiagramModel(reference_grazing_diagram())
    veg = zeros(3, 2, 3, 3)   # (SoilMoisture, GrazingPressure, CurrentVegetation, Vegetation)
    veg[1, 1, 1, :] = [0.5, 0.35, 0.15]
    veg[1, 1, 2, :] = [0.3, 0.4, 0.3]
    veg[1, 1, 3, :] = [0.15, 0.35, 0.5]
    veg[1, 2, 1, :] = [0.85, 0.12, 0.03]
    veg[1, 2, 2, :] = [0.7, 0.25, 0.05]
    veg[1, 2, 3, :] = [0.5, 0.35, 0.15]
    veg[2, 1, 1, :] = [0.3, 0.4, 0.3]
    veg[2, 1, 2, :] = [0.15, 0.35, 0.5]
    veg[2, 1, 3, :] = [0.05, 0.25, 0.7]
    veg[2, 2, 1, :] = [0.7, 0.25, 0.05]
    veg[2, 2, 2, :] = [0.5, 0.35, 0.15]
    veg[2, 2, 3, :] = [0.3, 0.4, 0.3]
    veg[3, 1, 1, :] = [0.15, 0.35, 0.5]
    veg[3, 1, 2, :] = [0.05, 0.25, 0.7]
    veg[3, 1, 3, :] = [0.03, 0.12, 0.85]
    veg[3, 2, 1, :] = [0.5, 0.35, 0.15]
    veg[3, 2, 2, :] = [0.3, 0.4, 0.3]
    veg[3, 2, 3, :] = [0.15, 0.35, 0.5]
    m = bind_cpt(m,
                 [:Climate => [0.3, 0.5, 0.2],
                  :ClimateForecast => [0.7 0.2 0.1; 0.15 0.7 0.15; 0.1 0.2 0.7],
                  :SoilMoisture => [0.7 0.25 0.05; 0.3 0.5 0.2; 0.05 0.3 0.65],
                  :CurrentVegetation => [0.3, 0.4, 0.3],
                  :GrazingPressure => [0.95 0.05; 0.6 0.4; 0.15 0.85],
                  :Vegetation => veg,
                  :HabitatQuality => [0.85 0.15; 0.4 0.6; 0.15 0.85],
                  :Occupancy => [0.8 0.2; 0.25 0.75],
                  :Biodiversity => [0.9 0.1; 0.3 0.7]])
    return bind_utility(m,
                        [:ConservationBenefit => [0.0, 100.0],
                         :ManagementCost => [-40.0, -15.0, 0.0]])
end

"""
    two_stage_diagram() -> InfluenceDiagram

A two-decision test-then-act problem (a small oil-wildcatter): chance `Oil` (dry, wet);
decision `Test` (test, skip) with no information; chance `Result` (pos, neg, none)
depending on `(Oil, Test)`; decision `Drill` (drill, dont) informed by `(Test, Result)`,
so the diagram has no-forgetting; utilities `Payoff(Oil, Drill)` and `TestCost(Test)`.
"""
function two_stage_diagram()
    return influence_diagram(:Oil => [:dry, :wet], :Test => [:test, :skip],
                             :Result => [:pos, :neg, :none], :Drill => [:drill, :dont];
                             mechanisms=[:Result => (:Oil, :Test)],
                             decisions=[:Test => Symbol[], :Drill => (:Test, :Result)],
                             utilities=[:Payoff => (:Oil, :Drill), :TestCost => :Test])
end

"""
    two_stage_model() -> InfluenceDiagramModel

[`two_stage_diagram`](@ref) with `P(Oil = wet) = 0.5`, a test that reports `pos`
with probability 0.8 when wet and 0.3 when dry (and always `none` when skipped),
payoff 100 for drilling a wet site, -60 for drilling a dry one, 0 for not drilling,
and a test cost of 10. The optimal strategy tests and drills exactly on a positive
result, with maximal expected utility 21 (against 20 without testing). Being told the
oil state before the test decision is worth 29
(`expected_value_of_information(two_stage_model(), :Oil, :Test)`), which is the
non-degenerate sequential value-of-information example of the test suite and of
vignette 04.
"""
function two_stage_model()
    m = InfluenceDiagramModel(two_stage_diagram())
    res = zeros(2, 2, 3)   # (Oil, Test, Result)
    res[1, 1, :] = [0.3, 0.7, 0.0]
    res[2, 1, :] = [0.8, 0.2, 0.0]
    res[1, 2, :] = [0.0, 0.0, 1.0]
    res[2, 2, :] = [0.0, 0.0, 1.0]
    m = bind_cpt(m, [:Oil => [0.5, 0.5], :Result => res])
    return bind_utility(m, [:Payoff => [-60.0 0.0; 100.0 0.0], :TestCost => [-10.0, 0.0]])
end

"""
    used_car_buyer_model() -> InfluenceDiagramModel

The used car buyer of [Howard1977](@cite), with the numbers of the DecisionProgramming.jl
documentation (profits in US dollars, the source's own). A car is a `lemon` with
probability 0.2 and a `peach` otherwise (`Car`). The buyer first decides whether to
`Test` it, for 25 dollars; the `Result` is `no_test`, or the car's kind exactly. The
`Purchase` (`without_guarantee`, `with_guarantee`, `none`) sees the result and nothing
else. Buying pays 100 without the guarantee and 40 with it, less repairs: 200 for a lemon
and 40 for a peach without the guarantee, nothing for a lemon and 20 for a peach with it.

`Purchase` does not observe `Test`, so the diagram has no no-forgetting and
[`DecisionVariableElimination`](@ref) refuses it, although the result says whether a test
was made. The optimum is to test, buy a lemon with the guarantee and a peach without, for
an expected profit of 31; without the test the best is 28.
"""
function used_car_buyer_model()
    id = influence_diagram(:Car => [:lemon, :peach], :Test => [:no_test, :test],
                           :Result => [:no_test, :lemon, :peach],
                           :Purchase => [:without_guarantee, :with_guarantee, :none];
                           mechanisms=[:Result => (:Car, :Test)],
                           decisions=[:Test => (), :Purchase => :Result],
                           utilities=[:Fee => :Test, :Profit => :Purchase,
                                      :Repairs => (:Car, :Purchase)])
    result = zeros(2, 2, 3)                    # (car, test) -> result
    result[1, 1, :] = [1, 0, 0]
    result[1, 2, :] = [0, 1, 0]
    result[2, 1, :] = [1, 0, 0]
    result[2, 2, :] = [0, 0, 1]
    m = bind_cpt(InfluenceDiagramModel(id), [:Car => [0.2, 0.8], :Result => result])
    return bind_utility(m,
                        [:Fee => [0.0, -25.0], :Profit => [100.0, 40.0, 0.0],
                         :Repairs => [-200.0 0.0 0.0; -40.0 -20.0 0.0]])
end

"""
    pig_breeding_model(; months = 4) -> InfluenceDiagramModel

The pig breeding problem of [LauritzenNilsson2001](@cite), the standard limited-memory
influence diagram, with their numbers (Danish kroner, the source's own). A pig is grown
for `months` months and sold: for 300 if it is ill then, for 1000 if healthy (`Sale`). It
is ill at the start with probability 0.1 (`Health1`). In each month but the last a test
(`Test_k`) is positive with probability 0.8 for an ill pig and 0.1 for a healthy one, and
the decision `Treat_k` (`treat`, `pass`) sees **that month's test only**. Treating costs
100 (`Cost_k`). An ill pig stays ill with probability 0.5 if treated and 0.9 if not; a
healthy one falls ill with probability 0.1 if treated and 0.2 if not.

With four months the optimum is 726.8121: do not treat in the first month whatever the
test says, and treat on a positive test in the second and third. The number of joint
states is `2^(3 months - 2)`, and the clusters of [`rooted_junction_tree`](@ref) stay at
eight states whatever `months` is.
"""
function pig_breeding_model(; months::Integer=4)
    months >= 2 || throw(ArgumentError("months must be at least 2, got $(months)"))
    health = [Symbol(:Health, k) for k in 1:months]
    tests = [Symbol(:Test, k) for k in 1:(months - 1)]
    treat = [Symbol(:Treat, k) for k in 1:(months - 1)]
    costs = [Symbol(:Cost, k) for k in 1:(months - 1)]
    id = influence_diagram((h => [:ill, :healthy] for h in health)...,
                           (t => [:positive, :negative] for t in tests)...,
                           (d => [:treat, :pass] for d in treat)...;
                           mechanisms=vcat([tests[k] => health[k] for k in 1:(months - 1)],
                                           [health[k + 1] => (health[k], treat[k])
                                            for k in 1:(months - 1)]),
                           decisions=[treat[k] => tests[k] for k in 1:(months - 1)],
                           utilities=vcat([costs[k] => treat[k] for k in 1:(months - 1)],
                                          [:Sale => health[end]]))
    next = zeros(2, 2, 2)                      # (health, treat) -> next health
    next[1, 1, :] = [0.5, 0.5]
    next[1, 2, :] = [0.9, 0.1]
    next[2, 1, :] = [0.1, 0.9]
    next[2, 2, :] = [0.2, 0.8]
    m = bind_cpt(InfluenceDiagramModel(id), health[1] => [0.1, 0.9])
    for k in 1:(months - 1)
        m = bind_cpt(m, [tests[k] => [0.8 0.2; 0.1 0.9], health[k + 1] => next])
        m = bind_utility(m, costs[k] => [-100.0, 0.0])
    end
    return bind_utility(m, :Sale => [300.0, 1000.0])
end
