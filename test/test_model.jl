@testset "InfluenceDiagramModel" begin
    @testset "construction and accessors" begin
        m = InfluenceDiagramModel(umbrella_diagram())
        @test syntax(m) isa InfluenceDiagram
        @test bayes_model(m) isa BayesModel
        @test haskey(spaces(m), :Umbrella)
        @test isempty(kernels(m)) && isempty(evidence(m)) && isempty(history(m))
        @test isempty(bound_utilities(m)) && length(strategy(m)) == 0
        @test Set(missing_kernels(m)) == Set([:Weather, :Forecast])
        @test !has_semantics(m)
        @test space(m, :Umbrella) == FiniteSpace(:Umbrella, [:take, :leave])
        @test parent_space(m, :Forecast) == FiniteSpace(:Weather, [:sunny, :rainy])
        m = umbrella_model()
        @test has_semantics(m)
        @test kernel(m, :Weather).table == [0.7, 0.3]
        @test intervened_variables(m) == Symbol[]
        @test !is_intervened(m, :Weather)
        @test m == umbrella_model()
        @test hash(m) == hash(umbrella_model())
        @test m ≈ umbrella_model()
        @test !(m ≈ fix_decision(m, :Umbrella => :take))
        @test extras(m) isa Dict{Symbol,Any}
    end

    @testset "bind_utility" begin
        m = InfluenceDiagramModel(umbrella_diagram())
        @test utility_ref(syntax(m), :U) == NoRef()
        m1 = bind_utility(m, :U => [20.0 100.0; 70.0 0.0])
        @test utility_ref(syntax(m1), :U) == NamedRef("U")
        @test utility_ref(syntax(m), :U) == NoRef()   # immutable
        u = utility(m1, :U)
        @test u isa TabularUtility
        @test scope(u) == [:Weather, :Umbrella]
        @test utility_value(u, :rainy, :take) == 70.0
        @test utility_value(u,
                            Dict(:Weather => :sunny, :Umbrella => :leave,
                                 :Forecast => :sunny)) ==
              100.0
        @test_throws UtilityScopeError utility_value(u, :rainy)
        @test_throws UtilityScopeError bind_utility(m, :U => [1.0, 2.0])
        m2 = bind_utility(m,
                          :U => (w, a) -> w == :rainy ? (a == :take ? 70 : 0) :
                                          (a == :take ? 20 : 100))
        @test utility(m2, :U) isa FunctionUtility
        @test utility_table(utility(m2, :U), utility(m1, :U).scope) ==
              [20.0 100.0; 70.0 0.0]
        @test utility_factor(utility(m2, :U), utility(m1, :U).scope) ==
              utility_factor(utility(m1, :U))
        @test m1 ≈ m2
        @test total_utility(m1, Dict(:Weather => :rainy, :Umbrella => :take)) == 70.0
        @test total_utility(m1, [:Weather => :sunny, :Umbrella => :take]) == 20.0
        # a ready-made utility with the wrong scope
        wrong = TabularUtility([FiniteAxis(:Weather, [:sunny, :rainy])], [1.0, 2.0])
        @test_throws UtilityScopeError bind_utility(m, :U => wrong)
        @test_throws UtilityScopeError TabularUtility([FiniteAxis(:W, [:a, :b])],
                                                      [1.0, 2.0, 3.0])
        bad_f = FunctionUtility([:Weather, :Umbrella], (w, a) -> "no")
        @test_throws UtilityScopeError utility_value(bad_f, :sunny, :take)
        # binding an unbound-scope utility through a model whose utility node is empty
        e = influence_diagram(:X => [:a, :b]; utilities=[:K => Symbol[]])
        me = bind_utility(InfluenceDiagramModel(e), :K => 5.0)
        @test utility_value(utility(me, :K)) == 5.0
        @test utility_table(utility(me, :K)) == fill(5.0)
    end

    @testset "fix_decision and set_policy" begin
        m = umbrella_model()
        m1 = fix_decision(m, :Umbrella => :take)
        @test strategy(m1)[:Umbrella] == ConstantPolicy(:take)
        @test length(strategy(m)) == 0
        @test syntax(m1) == syntax(m)    # no syntax change
        @test_throws UnknownStateError fix_decision(m, :Umbrella => :fly)
        @test_throws UnknownDecisionError fix_decision(m, :Weather => :sunny)
        p = deterministic_policy(m, :Umbrella, f -> f == :rainy ? :take : :leave)
        m2 = set_policy(m, :Umbrella, p)
        @test strategy(m2)[:Umbrella] == p
        @test set_policy(m, Strategy(:Umbrella => p)) == m2
        @test unset_policy(m2, :Umbrella) == m
        @test unset_policy(m2) == m
        @test fix_decision(m, [:Umbrella => :leave]) == fix_decision(m, :Umbrella => :leave)
    end

    @testset "observe" begin
        m = umbrella_model()
        m1 = observe(m, :Forecast => :rainy)
        @test evidence(m1) == Dict(:Forecast => :rainy)
        @test isempty(evidence(m))
        @test unobserve(m1, :Forecast) == m
        @test unobserve(observe(m, [:Forecast => :rainy, :Weather => :rainy])) == m
        @test_throws UnknownStateError observe(m, :Forecast => :foggy)
    end

    @testset "do_intervention on a chance variable" begin
        m = umbrella_model()
        m1 = do_intervention(m, :Weather => :rainy)
        @test intervened_variables(m1) == [:Weather]
        @test is_intervened(m1, :Weather)
        @test length(history(m1)) == 1
        @test history(m1)[1].kind == :hard
        @test nparts(syntax(m1), :Decision) == 1
        @test kernel_ref(syntax(m1), mechanism_of(syntax(m1), :Weather)) ==
              PointMassRef(:rainy)
        @test kernel(m1, :Weather).table == [0.0, 1.0]
        @test syntax(m) == syntax(umbrella_model())   # the original is untouched
        @test_throws UnknownStateError do_intervention(m, :Weather => :foggy)
        @test do_intervention(m, [:Weather => :rainy]) ≈ m1
        # fixing the umbrella under do(Weather = rainy)
        @test expected_utility(m1, :Umbrella => :take) ≈ 70.0
        @test expected_utility(m1, :Umbrella => :leave) ≈ 0.0
    end

    @testset "do_intervention on a decision differs from fix_decision" begin
        m = umbrella_model()
        fixed = fix_decision(m, :Umbrella => :take)
        done = do_intervention(m, :Umbrella => :take)
        # structurally different: the decision is gone and a constant mechanism is in
        @test nparts(syntax(fixed), :Decision) == 1
        @test nparts(syntax(done), :Decision) == 0
        @test nparts(syntax(done), :InformationInput) == 0
        @test has_mechanism(syntax(done), :Umbrella)
        @test !has_mechanism(syntax(fixed), :Umbrella)
        @test kernel_ref(syntax(done), mechanism_of(syntax(done), :Umbrella)) ==
              PointMassRef(:take)
        @test isempty(strategy(done)) && length(strategy(fixed)) == 1
        @test occursin("removed decision", history(done)[1].note)
        @test validate(done; closed=true, semantics=true, strategy=true) === nothing
        # same expected utility for the same action
        @test expected_utility(fixed) ≈ 35.0
        # the intervened model has no decision: its expected utility is that of the
        # network directly
        bn_done = instantiate(done)
        @test expected_utility(bn_done) ≈ 35.0
        @test optimize(done).expected_utility ≈ 35.0
        # without information the two coincide for every action
        noinfo = without_information(m, :Umbrella, :Forecast)
        for a in (:take, :leave)
            @test expected_utility(fix_decision(noinfo, :Umbrella => a)) ≈
                  expected_utility(instantiate(do_intervention(noinfo, :Umbrella => a)))
        end
        # do on a decision with a policy drops the policy
        m3 = do_intervention(fix_decision(m, :Umbrella => :leave), :Umbrella => :take)
        @test isempty(strategy(m3))
    end

    @testset "soft_intervention" begin
        m = umbrella_model()
        k = cpt(FiniteAxis[], FiniteAxis(:Weather, [:sunny, :rainy]), [0.5, 0.5])
        m1 = soft_intervention(m, :Weather => k)
        @test kernel(m1, :Weather).table == [0.5, 0.5]
        @test history(m1)[1].kind == :soft
        @test intervened_variables(m1) == [:Weather]
        # on a decision: the decision is removed
        kd = cpt(FiniteAxis[], FiniteAxis(:Umbrella, [:take, :leave]), [0.5, 0.5])
        m2 = soft_intervention(fix_decision(m, :Umbrella => :take), :Umbrella => kd)
        @test nparts(syntax(m2), :Decision) == 0
        @test isempty(strategy(m2))
        @test expected_utility(instantiate(m2)) ≈ 0.5 * 35 + 0.5 * 70
        # reference form with a kernel that does not fit
        @test_throws BayesNetError soft_intervention(m, :Weather => NamedRef("x");
                                                     kernel=kd)
    end

    @testset "information structure" begin
        m = umbrella_model()
        noinfo = without_information(m, :Umbrella, :Forecast)
        @test information_names(syntax(noinfo), :Umbrella) == Symbol[]
        @test information_names(syntax(m), :Umbrella) == [:Forecast]
        @test_throws InvalidInformationSetError without_information(m, :Umbrella, :Weather)
        back = with_information(noinfo, :Umbrella, :Forecast)
        @test canonicalize(syntax(back)) == canonicalize(syntax(m))
        @test validate(syntax(with_information(m, :Umbrella, :Weather))) === nothing
        @test_throws InvalidInformationSetError with_information(m, :Umbrella, :Forecast)
        # policies whose signature changed are dropped
        fixed = fix_decision(m, :Umbrella => :take)
        @test isempty(strategy(with_information(fixed, :Umbrella, :Weather)))
        # a variable downstream of the action cannot be added
        @test_throws InvalidInformationSetError with_information(two_stage_model(), :Test,
                                                                 :Result)
        @test variable_name.(Ref(syntax(m)), admissible_information(m, :Umbrella)) ==
              [:Weather]
        @test variable_name.(Ref(syntax(noinfo)),
                             admissible_information(noinfo, :Umbrella)) ==
              [:Weather, :Forecast]
    end

    @testset "with_information propagates no-forgetting" begin
        t = two_stage_model()
        # the arc reaches every decision after the one it was added to
        a = with_information(t, :Test, :Oil)
        @test information_names(syntax(a), :Test) == [:Oil]
        @test information_names(syntax(a), :Drill) == [:Test, :Result, :Oil]
        @test is_no_forgetting(a)
        # both policies are dropped, since both signatures changed
        fixed = fix_decision(t, [:Test => :test, :Drill => :drill])
        @test isempty(strategy(with_information(fixed, :Test, :Oil)))
        # the last decision has nothing after it
        b = with_information(t, :Drill, :Oil)
        @test information_names(syntax(b), :Drill) == [:Test, :Result, :Oil]
        @test information_names(syntax(b), :Test) == Symbol[]
        # opting out keeps the single-arc (limited-memory) semantics
        c = with_information(t, :Test, :Oil; no_forgetting=false)
        @test information_names(syntax(c), :Drill) == [:Test, :Result]
        @test !is_no_forgetting(c)
        @test haskey(strategy(with_information(fixed, :Test, :Oil; no_forgetting=false)),
                     :Drill)
    end

    @testset "heterogeneous bind_utility vectors" begin
        id = influence_diagram(:W => [:sunny, :rainy], :D => [:take, :leave];
                               mechanisms=[:W => ()], decisions=[:D => Symbol[]],
                               utilities=[:U => (:W, :D), :K => ()])
        m = bind_cpt(InfluenceDiagramModel(id), :W => [0.5, 0.5])
        # element type Pair{Symbol,Any}: a table and a number in one call
        m = bind_utility(m, [:U => [20.0 100.0; 70.0 0.0], :K => 5.0])
        @test utility(m, :K) == TabularUtility(FiniteAxis[], 5.0)
        @test scope(utility(m, :U)) == [:W, :D]
        @test optimize(m).expected_utility ≈ 50.0 + 5.0
        @test_throws UtilityScopeError bind_utility(m, [:U => "not a table"])
    end

    @testset "validate on models" begin
        m = umbrella_model()
        @test validate(m) === nothing
        @test validate(m; closed=true, unique_names=true, semantics=true) === nothing
        bad = InfluenceDiagramModel(syntax(m); kernels=kernels(m),
                                    utilities=Dict{Symbol,AbstractUtility}(:U => TabularUtility([FiniteAxis(:Weather,
                                                                                                            [:sunny,
                                                                                                             :rainy])],
                                                                                                [1.0,
                                                                                                 2.0])))
        @test_throws UtilityScopeError validate(bad)
    end

    @testset "validate forwards atol (a model read at a looser tolerance)" begin
        # rows off by 5e-8: fine at the atol the file was read with, not at the default
        id = umbrella_diagram()
        m = InfluenceDiagramModel(id)
        m = bind_cpt(m,
                     [:Weather => [0.7, 0.30000005],
                      :Forecast => [0.7 0.2 0.1; 0.15 0.25 0.6]]; atol=1e-6)
        m = bind_utility(m, :U => [20.0 100.0; 70.0 0.0])
        @test_throws BayesNetError validate(m)
        @test validate(m; atol=1e-6) === nothing
        @test validate(m; closed=true, unique_names=true, semantics=true, atol=1e-6) ===
              nothing
        # the same tolerance reaches the solvers and the reference algorithm
        @test_throws BayesNetError optimize(m)
        @test isapprox(optimize(m; atol=1e-6).expected_utility, 77.0; atol=1e-5)
        @test isapprox(optimize(m; backend=ExhaustivePolicySearch(),
                                atol=1e-6).expected_utility, 77.0; atol=1e-5)
        # instantiate validates at the given tolerance too (the brute-force
        # expected_utility then goes through BayesianNetworks.joint_distribution, which
        # has no atol of its own, so the reference algorithm still needs a normalised
        # model)
        @test instantiate(m, Strategy(:Umbrella => ConstantPolicy(:take)); atol=1e-6) isa
              BayesModel
        @test_throws BayesNetError instantiate(m,
                                               Strategy(:Umbrella => ConstantPolicy(:take)))
    end
end
