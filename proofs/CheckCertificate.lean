/-
`lake exe check_certificate DIAGRAM.json CERTIFICATE.json`

Reads a diagram written by InfluenceDiagrams.jl's `write_json_influence_diagram` and a certificate
written by `export_dve_certificate` (serialized with `JSON3.write`), parses both with
`Lean.Json.parse`, decodes the diagram with the proved checked decoder `Records.decodeDiagramChecked`
(`Finite/DVE/JsonRecords.lean`) and the certificate with the proved decoder
`DVECertificate.decodeCertificate` (`Finite/DVE/CertificateJson.lean`), and decides
`DVECertificate.certificateMatches` (`Finite/DVE/CertificateCheck.lean`), printing

    diagram: valid
    certificate: decoded
    variables: ok|FAIL                (each component of `Matches`)
    ...
    matches: yes|no
    nonnegative: yes|no               (`Nonneg`)
    exactly normalised: yes|no        (`ExactNormalised`)
    theorem certificate_tables: applies|does not apply
    theorem certificate_solve_spec: applies|does not apply
    normalisation error epsilon: 5.551115e-17  (`certificateEpsilon`, max |row sum - 1|)
    chance variables n: 2                      (`certChanceCount`)
    utility bound Umax: 1.000000e2             (`certUmax`)
    optimality gap 2e: 8.881784e-14            (`certificateBound`)
    theorem certificate_approx_optimal: applies|does not apply

(the numbers shown are the umbrella's binary64 certificate). The four numbers are exact rationals computed by the definitions named, printed in scientific
notation with seven significant digits, truncated (`sci`). `certificate_approx_optimal` applies
when the certificate matches, its cells are nonnegative and `certificateEpsilon < 1`; the gap is
then the bound on how far the exact DVE run's policy on the certificate's data can fall short of
the optimum of the row-normalised model.

A version-2 certificate (`export_dve_certificate(m; solution = true)`) is decoded by
`DVECertificate.decodeAnyCertificate` (`Finite/DVE/SolutionJson.lean`); its recorded solution is
then compared with the exact run of `Finite/DVE/SolutionRun.lean` on Julia's elimination order
(`Finite/DVE/SolutionCheck.lean`), printing

    solution: decoded
    solution arithmetic: binary64|exact_rational
    solution data: f64|q
    solution exact fallback: yes|no
    solution plan: ok|FAIL            (`solutionPlan`: Julia's order is a DVE plan)
    solution entries: 6
    exact value: 7.700000e1           (`valueT`)
    recorded value: 7.700000e1
    value discrepancy: 0              (|recorded - exact|)
    actions agree: yes|no             (`actionsAgree`)
    actions differing: 0
    action loss: 0                    (largest row maximum minus the score of the recorded action)
    score discrepancy: 0              (largest |recorded score - row maximum|)
    solutionMatches: yes|no           (`solutionMatches`, the exact comparison)
    tolerances tau tauv: 1.000000e-9 1.000000e-9
    solutionWithin: yes|no            (`solutionWithin tau tauv`, the binary64 comparison)
    theorem recorded_solution_optimal: applies|does not apply
    theorem recorded_solution_approx_optimal: applies|does not apply
    theorem recorded_binary64_approx_optimal: applies|does not apply

    theorem recorded_binary64_near_optimal: applies|does not apply
    solutionMatchesE: yes|no          (`solutionMatchesE`, the sliced run with hard evidence)
    solutionWithinE: yes|no           (`solutionWithinE tau tauv`)

The exact comparison is the verdict for a run with `arithmetic = "exact_rational"`, the binary64
comparison (fixed tolerances `tau = tauv = 10^-9`) for a binary64 run.
`recorded_solution_optimal` applies to a matching, nonnegative, exactly normalised certificate
whose solution satisfies `solutionMatches`; `recorded_solution_approx_optimal` replaces exact
normalisation by `certificateEpsilon < 1`; `recorded_binary64_approx_optimal` and
`recorded_binary64_near_optimal` need `solutionWithin tau tauv` and `certificateEpsilon < 1`.

A certificate with hard evidence rows is compared with the exact run on its data sliced at the
observed states (`Finite/DVE/SolutionEvidence.lean`, `Finite/DVE/SolutionCheckEvidence.lean`),
on Julia's order with the observed variables put back (`solutionPlanE`): the plan, entries,
values and loss lines then describe that run, `evidence probability` is its final mass
(`massST`), `solutionMatches`/`solutionWithin` print `solutionMatchesE`/`solutionWithinE`, and
the theorem lines are `recorded_solution_optimal_evidence`,
`recorded_solution_approx_optimal_evidence` and `recorded_binary64_near_optimal_evidence`.

The exit code is 0 exactly when the certificate matches and, for version 2, the solution passes
the comparison of its run's arithmetic. The parse and this printing code are trusted, not proved;
every verdict printed is a `decide` of a proved checker's propositions, and every number is
computed by the definitions named.
-/
import InfluenceDiagramsProofs.Finite.DVE.SolutionCheckEvidence
import Lean.Data.Json.Parser

open BayesianNetworksProofs.Raw InfluenceDiagramsProofs.Records InfluenceDiagramsProofs.DVECertificate
open InfluenceDiagramsProofs.DVECertificate.Spec

def verdict (b : Bool) : String := if b then "ok" else "FAIL"

def yesNo (b : Bool) : String := if b then "yes" else "no"

/-- `10 ^ k ≤ n / d` for an integer exponent `k`. -/
def atLeastPow (n d : Nat) (k : Int) : Bool :=
  if 0 ≤ k then d * 10 ^ k.toNat ≤ n else d ≤ n * 10 ^ (-k).toNat

/-- A rational in scientific notation with `p` significant digits, truncated (printing only:
trusted, not proved). -/
def sci (q : ℚ) (p : Nat := 7) : String :=
  if q = 0 then "0" else
    let sign := if q < 0 then "-" else ""
    let n := q.num.natAbs
    let d := q.den
    let k0 : Int := (toString n).length - (toString d).length
    let k : Int := if atLeastPow n d k0 then k0 else k0 - 1
    let s : Int := (p : Int) - 1 - k
    let m : Nat := if 0 ≤ s then n * 10 ^ s.toNat / d else n / (d * 10 ^ (-s).toNat)
    let ms := toString m
    s!"{sign}{ms.take 1}.{ms.drop 1}e{k}"

/-- The components of `Matches`, decided one by one. -/
def components (r : Diagram) (c : Certificate) : List (String × Bool) :=
  [("variables", decide (c.vars.length = r.nv ∧
      ∀ v : Fin r.nv, OptHolds (VariableOk r c.pool v) c.vars[v.val]?)),
    ("mechanisms", decide (c.mechanisms.length = r.nm ∧
      ∀ m : Fin r.nm, OptHolds (MechanismOk r c.pool m) c.mechanisms[m.val]?)),
    ("decisions", decide (c.decisions.length = r.nd ∧
      ∀ d : Fin r.nd, OptHolds (DecisionOk r d) c.decisions[d.val]?)),
    ("precedence", decide (c.precedence.length = r.np ∧
      ∀ p : Fin r.np, OptHolds (PrecedenceOk r p) c.precedence[p.val]?)),
    ("utilities", decide (c.utilities.length = r.nu ∧
      ∀ j : Fin r.nu, OptHolds (UtilityOk r c.pool j) c.utilities[j.val]?)),
    ("topological order", decide (c.topological.length = r.nv ∧ c.topological.Nodup ∧
      (∀ v ∈ c.topological, v < r.nv) ∧
      c.topological.Pairwise (fun a b => ¬ Arc r b a ∧ ¬ EvidenceArc r c.hard b a))),
    ("decision order", decide (c.decisionOrder.length = r.nd ∧ c.decisionOrder.Nodup ∧
      (∀ d ∈ c.decisionOrder, d < r.nd) ∧
      c.decisionOrder = c.topological.filterMap (decisionOf r))),
    ("no-forgetting", decide (c.decisionOrder.Pairwise (Remembers r))),
    ("evidence", decide ((c.hard.map HardEntry.var).Pairwise (· < ·) ∧
      ∀ e ∈ c.hard, e.stateIndex < dim r e.var ∧ ∀ d : Fin r.nd,
        (r.decisions d).action.val ≠ e.var)),
    ("reference pool", decide (c.pool.Nodup ∧ ∀ k : Fin c.pool.length,
      (∃ e ∈ c.vars, e.spaceRef = k.val) ∨ (∃ e ∈ c.mechanisms, e.kernelRef = k.val) ∨
        ∃ e ∈ c.utilities, e.utilityRef = k.val)),
    ("numbers", decide (c.numeric.normalization = "none" ∧
      (∀ x ∈ allValues c, ShapeOk c.numeric x) ∧ (∀ x ∈ allValues c, ValueOk x) ∧
      (BayesianNetworksProofs.Binary64.field c.tolerances.kernel ≠ 2047 ∧
        BayesianNetworksProofs.Binary64.field c.tolerances.decision ≠ 2047)))]


/-- The largest value of a score row (printing only). -/
def rowMax {n : Nat} (f : Fin n → ℚ) : ℚ :=
  (List.finRange n).foldr (fun b m => max (f b) m) (if h : 0 < n then f ⟨0, h⟩ else 0)

/-- Per-entry comparison statistics: (entries, differing actions, action loss, score
discrepancy), computed from the proved definitions `bucketAt`, `rowScore`, `entryIndex`. -/
def solutionStats (r : Diagram) (h : r.Valid) (c : Certificate) (s : Solution)
    (bk : Fin r.nd → Option (List (TVal r))) : Nat × Nat × ℚ × ℚ := Id.run do
  let mut n := 0
  let mut bad := 0
  let mut loss : ℚ := 0
  let mut disc : ℚ := 0
  for d in List.finRange r.nd do
    match s.policies[d.val]?, bk d with
    | some p, some B =>
      for e in p.entries do
        let f := rowScore r h B d p e
        let i := entryIndex c p e
        let m := rowMax f
        n := n + 1
        if !(decide (EntryAction f i)) then bad := bad + 1
        if hi : i < r.stateCount (r.decisions d).action then
          loss := max loss (m - f ⟨i, hi⟩)
        else loss := max loss 1
        disc := max disc |e.score.toRat - m|
    | _, _ => bad := bad + 1
  return (n, bad, loss, disc)

def arithmeticName : Arithmetic → String
  | .binary64 => "binary64"
  | .exactRational => "exact_rational"

def dataName : DataKind → String
  | .f64 => "f64"
  | .q => "q"

/-- The fixed tolerances of the binary64 comparison. -/
def tau : ℚ := 1 / 10 ^ 9

def readJson (path : String) : IO (Except String Lean.Json) := do
  let text ← IO.FS.readFile path
  return Lean.Json.parse text

def main (args : List String) : IO UInt32 := do
  match args with
  | [dpath, cpath] =>
    let dj ← readJson dpath
    let cj ← readJson cpath
    match dj, cj with
    | .error e, _ =>
      IO.println s!"error: diagram is not JSON: {e}"
      return 1
    | _, .error e =>
      IO.println s!"error: certificate is not JSON: {e}"
      return 1
    | .ok dj, .ok cj =>
      match decodeDiagramChecked dj with
      | none =>
        IO.println "diagram: invalid"
        return 1
      | some ⟨r, h⟩ =>
        IO.println "diagram: valid"
        match decodeAnyCertificate cj with
        | .error e =>
          IO.println s!"certificate: error: {e}"
          return 1
        | .ok (c, sol?) =>
          IO.println s!"certificate: decoded (version {if sol?.isSome then 2 else 1})"
          for (name, ok) in components r c do
            IO.println s!"{name}: {verdict ok}"
          let m := decide (certificateMatches r h c)
          let nn := decide (Nonneg c)
          let en := decide (ExactNormalised r c)
          IO.println s!"matches: {yesNo m}"
          IO.println s!"nonnegative: {yesNo nn}"
          IO.println s!"exactly normalised: {yesNo en}"
          IO.println s!"evidence rows: {c.hard.length}"
          IO.println s!"theorem certificate_tables: {if m && nn then "applies" else "does not apply"}"
          IO.println s!"theorem certificate_solve_spec: {if m && nn && en then "applies" else "does not apply"}"
          let eps := certificateEpsilon c
          IO.println s!"normalisation error epsilon: {sci eps}"
          IO.println s!"chance variables n: {certChanceCount c}"
          IO.println s!"utility bound Umax: {sci (certUmax c)}"
          let ok := m && nn && decide (eps < 1)
          IO.println s!"optimality gap 2e: {if eps < 1 then sci (certificateBound c) else "-"}"
          IO.println s!"theorem certificate_approx_optimal: {if ok then "applies" else "does not apply"}"
          match sol? with
          | none => return if m then 0 else 1
          | some s =>
            IO.println "solution: decoded"
            IO.println s!"solution arithmetic: {arithmeticName s.arithmetic}"
            IO.println s!"solution data: {dataName s.data}"
            IO.println s!"solution exact fallback: {yesNo s.exactFallback}"
            -- the run is defined only for nonnegative cells (`certKernel_nonneg`), and the
            -- theorems only for a matching certificate
            let evid := !c.hard.isEmpty
            let swE := solutionWithinE r h.valid c s tau tau
            let smE := solutionMatchesE r h.valid c s
            let planV : Option (InfluenceDiagramsProofs.DVE.Plan (r.compile h.valid) Finset.univ) :=
              if evid then solutionPlanE r h.valid c s else solutionPlan r h.valid s
            match planV with
            | none =>
              IO.println "solution plan: FAIL"
              IO.println "solutionMatches: no"
              IO.println "solutionWithin: no"
              IO.println s!"solutionMatchesE: {yesNo smE}"
              IO.println s!"solutionWithinE: {yesNo swE}"
              return 1
            | some plan =>
              IO.println "solution plan: ok"
              let (ne, bad, loss, disc) :=
                if evid then solutionStats r h.valid c s (bucketAtS r h.valid plan (initCT r h.valid c))
                else solutionStats r h.valid c s (bucketAt r h.valid plan (initT r h.valid c))
              let exact := if evid then valueST r h.valid plan (initCT r h.valid c)
                else valueT r h.valid plan (initT r h.valid c)
              let vdisc := |s.value.toRat - exact|
              IO.println s!"solution entries: {ne}"
              if evid then
                IO.println s!"evidence probability: {sci (massST r h.valid plan (initCT r h.valid c))}"
              IO.println s!"exact value: {sci exact}"
              IO.println s!"recorded value: {sci s.value.toRat}"
              IO.println s!"value discrepancy: {sci vdisc}"
              let agree := if evid then actionsAgreeE r h.valid c s else actionsAgree r h.valid c s
              IO.println s!"actions agree: {yesNo agree}"
              IO.println s!"actions differing: {bad}"
              IO.println s!"action loss: {sci loss}"
              IO.println s!"score discrepancy: {sci disc}"
              let sm := if evid then smE else solutionMatches r h.valid c s
              IO.println s!"solutionMatches: {yesNo sm}"
              IO.println s!"tolerances tau tauv: {sci tau} {sci tau}"
              let sw := if evid then swE else solutionWithin r h.valid c s tau tau
              IO.println s!"solutionWithin: {yesNo sw}"
              let ap (b : Bool) : String := if b then "applies" else "does not apply"
              if evid then
                IO.println s!"theorem recorded_solution_optimal_evidence: {ap (m && nn && en && sm)}"
                IO.println s!"theorem recorded_solution_approx_optimal_evidence: {ap (ok && sm)}"
                IO.println s!"theorem recorded_binary64_near_optimal_evidence: {ap (ok && sw)}"
              else
                IO.println s!"theorem recorded_solution_optimal: {ap (m && nn && en && sm)}"
                IO.println s!"theorem recorded_solution_approx_optimal: {ap (ok && sm)}"
                IO.println s!"theorem recorded_binary64_approx_optimal: {ap (ok && sw)}"
                IO.println s!"theorem recorded_binary64_near_optimal: {ap (ok && sw)}"
              IO.println s!"solutionMatchesE: {yesNo smE}"
              IO.println s!"solutionWithinE: {yesNo swE}"
              let pass := match s.arithmetic with
                | .exactRational => sm
                | .binary64 => sw
              return if m && pass then 0 else 1
  | _ =>
    IO.eprintln "usage: check_certificate DIAGRAM.json CERTIFICATE.json"
    return 2
