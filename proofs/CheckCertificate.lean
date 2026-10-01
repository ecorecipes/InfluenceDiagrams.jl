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

The exit code is 0 exactly when the certificate matches. The parse and this printing code are
trusted, not proved; every verdict printed is a `decide` of the proved checker's propositions.
-/
import InfluenceDiagramsProofs.Finite.DVE.CertificateCheck
import Lean.Data.Json.Parser

open BayesianNetworksProofs.Raw InfluenceDiagramsProofs.Records InfluenceDiagramsProofs.DVECertificate
open InfluenceDiagramsProofs.DVECertificate.Spec

def verdict (b : Bool) : String := if b then "ok" else "FAIL"

def yesNo (b : Bool) : String := if b then "yes" else "no"

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
          return if m then 0 else 1
  | _ =>
    IO.eprintln "usage: check_certificate DIAGRAM.json CERTIFICATE.json"
    return 2
