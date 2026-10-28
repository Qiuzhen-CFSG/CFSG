module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/BinaryException.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.G2.BinarySign
public import Theory.AtlasPort.LinearGroups.G2.Simplicity
public import Theory.AtlasPort.LinearGroups.G2.LocalFieldTransport

/-!
Transport from the two-element prime field proves the binary exception for
every field of order two. Together with simplicity above order two, this
gives the exact simplicity range of the full octonion automorphism model.
-/

@[expose] public section

namespace Atlas.G2
variable {F : Type*} [Field F] [Finite F]

noncomputable def binaryFieldEquiv (hF : Nat.card F=2) : F ≃+* ZMod 2 := by
  let := Fintype.ofFinite F
  exact (ZMod.ringEquivOfPrime F Nat.prime_two (by simpa [Nat.card_eq_fintype_card] using hF)).symm

 theorem card_longRootNormalClosure_binary (hF : Nat.card F=2) :
    Nat.card (longRootNormalClosure (F := F))=6048 := by
  rw [Nat.card_congr (longRootNormalClosureFieldEquiv (binaryFieldEquiv hF)).toEquiv]
  exact BinaryException.card_H

 theorem index_longRootNormalClosure_binary (hF : Nat.card F=2) :
    (longRootNormalClosure (F := F)).index=2 := by
  have hc := (longRootNormalClosure (F := F)).card_mul_index
  rw [card_longRootNormalClosure_binary hF,card_Model,hF] at hc
  norm_num at hc
  omega

 theorem not_simple_binary (hF : Nat.card F=2) : ¬ IsSimpleGroup (Model F) := by
  intro hs
  exact BinaryException.not_simple ((fieldEquiv (binaryFieldEquiv hF)).isSimpleGroup_congr.mp hs)

 theorem longRootNormalClosure_binary_nontrivial (hF : Nat.card F=2) :
    longRootNormalClosure (F := F) ≠ ⊥ := by
  intro h
  have hc := card_longRootNormalClosure_binary hF
  rw [h,Subgroup.card_bot] at hc
  contradiction

 theorem longRootNormalClosure_binary_proper (hF : Nat.card F=2) :
    longRootNormalClosure (F := F) ≠ ⊤ := by
  intro h
  have hi := index_longRootNormalClosure_binary hF
  rw [h,Subgroup.index_top] at hi
  contradiction

/-- Exact simplicity range of the full concrete octonion automorphism group. -/
theorem isSimple_iff : IsSimpleGroup (Model F) ↔ 2 < Nat.card F := by
  constructor
  · intro hs
    have hq : 1 < Nat.card F := Finite.one_lt_card (α := F)
    by_contra hn
    have he : Nat.card F=2 := by omega
    exact not_simple_binary he hs
  · exact isSimple

end Atlas.G2

