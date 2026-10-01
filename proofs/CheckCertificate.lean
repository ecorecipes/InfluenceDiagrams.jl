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

The exit code is 0 exactly when the certificate matches. The parse and this printing code are
trusted, not proved; every verdict printed is a `decide` of the proved checker's propositions.
-/
import InfluenceDiagramsProofs.Finite.DVE.CertificateApprox
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
        match decodeCertificate cj with
        | .error e =>
          IO.println s!"certificate: error: {e}"
          return 1
        | .ok c =>
          IO.println "certificate: decoded"
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
          return if m then 0 else 1
  | _ =>
    IO.eprintln "usage: check_certificate DIAGRAM.json CERTIFICATE.json"
    return 2
