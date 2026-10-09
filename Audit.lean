module

public import NearlyMinimax
public import RoughRegime
public import Solution
public import Lean.Util.CollectAxioms


@[expose] public section

/-! Audit every theorem declared by every imported project source module,
including generated/private declarations, selected submitted Solution proofs, and the vendored sources.
Audit definitions as well, and reject custom project axioms and all dependencies except the three
standard logical foundations. This verifies kernel trust, not paper coverage.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut ownModules : Std.HashSet Nat := {}
  let mut vendorModules : Std.HashSet Nat := {}
  let mut ownModuleNames : Array String := #[]
  let mut vendorModuleNames : Array String := #[]
  for mod in env.header.moduleNames do
    if let some idx := env.getModuleIdx? mod then
      if mod == `NearlyMinimax || mod == `Solution || "NearlyMinimax.".isPrefixOf mod.toString then
        ownModules := ownModules.insert idx
        ownModuleNames := ownModuleNames.push mod.toString
      if mod == `RoughRegime || "RoughRegime.".isPrefixOf mod.toString then
        vendorModules := vendorModules.insert idx
        vendorModuleNames := vendorModuleNames.push mod.toString
  let isOwn := fun n ↦ match env.getModuleIdxFor? n with
    | some idx => ownModules.contains idx
    | none => false
  let isVendor := fun n ↦ match env.getModuleIdxFor? n with
    | some idx => vendorModules.contains idx
    | none => false
  let isProject := fun n ↦ isOwn n || isVendor n
  for (n, ci) in env.constants.toList do
    if isProject n then
      if let .axiomInfo _ := ci then
        throwError "Project declares a custom axiom: {n}"
  let declarations := env.constants.toList.filter fun (n, _) ↦ isProject n
  let declarations := declarations.toArray.qsort fun a b ↦ a.1.toString < b.1.toString
  let mut rows : Array Json := #[]
  let mut ownTheorems := 0
  let mut vendorTheorems := 0
  for (n, ci) in declarations do
    let axioms ← collectAxioms n
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unapproved axiom {ax} in {n}"
    if ci.isTheorem then
      if isOwn n then ownTheorems := ownTheorems + 1
      if isVendor n then vendorTheorems := vendorTheorems + 1
      rows := rows.push (Json.mkObj [
        ("theorem", toJson n.toString),
        ("origin", toJson (if isOwn n then "NearlyMinimax" else "vendored_RoughRegime")),
        ("axioms", toJson ((axioms.map Name.toString).qsort (· < ·)))])
  logInfo (Json.mkObj [
    ("schema_version", toJson (1 : Nat)),
    ("project_module_count", toJson (ownModules.size + vendorModules.size)),
    ("nearly_minimax_module_count", toJson ownModules.size),
    ("vendored_module_count", toJson vendorModules.size),
    ("declaration_count", toJson declarations.size),
    ("theorem_count", toJson rows.size),
    ("nearly_minimax_modules", toJson (ownModuleNames.qsort (· < ·))),
    ("vendored_modules", toJson (vendorModuleNames.qsort (· < ·))),
    ("nearly_minimax_theorem_count", toJson ownTheorems),
    ("vendored_theorem_count", toJson vendorTheorems),
    ("allowed_axioms", toJson #["propext", "Classical.choice", "Quot.sound"]),
    ("axiom_audit_passed", toJson true),
    ("theorems", Json.arr rows)]).compress
