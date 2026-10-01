/-
`lake exe check_records FILE.json`

Reads a document written by InfluenceDiagrams.jl's `write_json_influence_diagram`, parses it with
`Lean.Json.parse`, decodes it with the proved decoder `Records.decodeDiagramChecked`
(`InfluenceDiagramsProofs/Finite/DVE/JsonRecords.lean`) and prints a canonical summary:

    format: influence-diagram-acset
    valid: yes
    valid with unique names: yes|no
    variables: <n>
    states <variable>: <label at position 1>, ...
    parents <target variable>: <slot 1 variable>, ...          (chance mechanisms)
    decision <decision>: <action variable>
    information <decision>: <variable at information_position 1>, ...
    policy <decision>: <info 1> [<labels>] x ... -> <action> [<labels>]
    utility <utility>: <variable at utility_position 1>, ...
    topological: <variable>, ...                                (instantiated chance part)
    acyclic: yes

`valid` is `decodeDiagramChecked` (`FullValid`, which includes the decision-precedence checks),
and `valid with unique names` is `decodeDiagramCheckedNames` (`FullValid` and `NamesUnique`), the
verdicts of Julia's `validate(...; closed = true)` and `validate(...; closed = true,
unique_names = true)`. `states` lines list `Raw.Tables.labelAt`, the compiled state labels in position order
(`Raw.Network.labelAt_eq`); `information` lines list `Raw.Tables.slotAt` of the decision's policy
mechanism in the instantiated chance part, its slot variables in `information_position` order
(`Raw.Network.slotAt_eq`, `decodeDiagramChecked_policyAxes`). The `policy` line is the policy-table
layout the label-order theorems read: the information axes in that order, each with its labels in
`state_position` order, then the action axis in `state_position` order, whose first maximizer is
the table entry (`solveRepRecords_table_of_fullValid`). `utility` lines are printed for comparison
only; no theorem here is about utility-scope order.

The parse (`Lean.Json.parse`) and this printing code are trusted, not proved.
-/
import InfluenceDiagramsProofs.Finite.DVE.JsonRecords
import Lean.Data.Json.Parser

open BayesianNetworksProofs.Raw InfluenceDiagramsProofs.Records

def joinLabels (xs : List String) : String := ", ".intercalate xs

/-- The summary lines of a checked diagram. -/
def summary (r : Diagram) (_h : r.FullValid) (names : Bool) : List String := Id.run do
  let t := r.chance
  let name (v : Fin r.nv) : String := (r.vars v).name
  let labels (v : Fin r.nv) : List String :=
    (List.range (r.stateCount v)).map fun a => (t.labelAt v a).getD "?"
  let mut out : List String :=
    ["format: influence-diagram-acset", "valid: yes",
      s!"valid with unique names: {if names then "yes" else "no"}", s!"variables: {r.nv}"]
  for v in List.finRange r.nv do
    out := out ++ [s!"states {name v}: {joinLabels (labels v)}"]
  for m in List.finRange r.nm do
    let count := (List.finRange r.ni).countP fun i => (r.inputs i).mechanism = m
    let slots := (List.range count).map fun j =>
      match t.slotAt (Fin.castAdd r.nd m) j with
      | some v => name v
      | none => "?"
    out := out ++ [s!"parents {name (r.mechanisms m).target}: {joinLabels slots}"]
  for d in List.finRange r.nd do
    let action := (r.decisions d).action
    let count := (List.finRange r.nf).countP fun f => (r.information f).decision = d
    let info := (List.range count).map fun j => t.slotAt (Fin.natAdd r.nm d) j
    let infoNames := info.map fun o => match o with
      | some v => name v
      | none => "?"
    let axes := info.map fun o => match o with
      | some v => s!"{name v} [{joinLabels (labels v)}]"
      | none => "?"
    out := out ++ [s!"decision {(r.decisions d).name}: {name action}",
      s!"information {(r.decisions d).name}: {joinLabels infoNames}",
      s!"policy {(r.decisions d).name}: {" x ".intercalate axes} -> {name action} [{joinLabels (labels action)}]"]
  for u in List.finRange r.nu do
    let count := (List.finRange r.nq).countP fun q => (r.utilityInputs q).utility = u
    let scope := (List.range count).map fun j =>
      match (List.finRange r.nq).find? (fun q =>
          (r.utilityInputs q).utility = u && (r.utilityInputs q).position = j) with
      | some q => name (r.utilityInputs q).var
      | none => "?"
    out := out ++ [s!"utility {(r.utilities u).name}: {joinLabels scope}"]
  match t.order with
  | some l => out := out ++ [s!"topological: {joinLabels (l.map name)}"]
  | none => out := out ++ ["topological: ?"]
  out := out ++ ["acyclic: yes"]
  return out

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let text ← IO.FS.readFile path
    match Lean.Json.parse text with
    | .error e =>
      IO.println s!"error: not JSON: {e}"
      return 1
    | .ok j =>
      match decodeDiagram j with
      | .error e =>
        IO.println s!"error: {e}"
        return 1
      | .ok r =>
        match decodeDiagramChecked j with
        | some ⟨r', h⟩ =>
          let names := (decodeDiagramCheckedNames j).isSome
          for line in summary r' h names do
            IO.println line
          return 0
        | none =>
          IO.println "format: influence-diagram-acset"
          IO.println "valid: no"
          IO.println "valid with unique names: no"
          IO.println s!"variables: {r.nv}"
          return 1
  | _ =>
    IO.eprintln "usage: check_records FILE.json"
    return 2
