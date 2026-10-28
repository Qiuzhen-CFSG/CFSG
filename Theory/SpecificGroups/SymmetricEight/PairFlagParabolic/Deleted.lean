module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Uses the ATLAS exceptional-isomorphism construction, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.SpecificGroups.SymmetricEight.PairFlagParabolic.Coordinates

/-!
# Recovering the four pairs from the deleted-module pencil

The two words 11110000 and 11001100 span a pencil modulo the constant word.
Its representatives are exactly the words constant on each pair and with
zero half-weight. The two distinguished words separate the four pair labels,
so preserving this pencil is equivalent to preserving the literal partition
{01,23,45,67}. The proof works for every permutation, before restricting to A₈.

A kernel certificate checks the representative criterion on the 256 binary
words; permutation invariance and recovery of the pairs are proved structurally.
Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
15.3.28(3), printed p.1131, using the ATLAS deleted-module coordinates.
-/

open Atlas.Order20160A8
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
namespace Theory.SpecificGroups.SymmetricEight.PairFlagParabolic
@[expose] public noncomputable section

def firstWord : DeletedEight.evenCode :=
  ⟨![1,1,1,1,0,0,0,0], by
    change (∑ i : Fin 8, (![1,1,1,1,0,0,0,0] : Fin 8 → ZMod 2) i) = 0
    decide⟩
def secondWord : DeletedEight.evenCode :=
  ⟨![1,1,0,0,1,1,0,0], by
    change (∑ i : Fin 8, (![1,1,0,0,1,1,0,0] : Fin 8 → ZMod 2) i) = 0
    decide⟩

def deletedPencil : Submodule (ZMod 2) DeletedEight.W :=
  Submodule.span (ZMod 2) {Submodule.Quotient.mk firstWord, Submodule.Quotient.mk secondWord}

private def pairConstant (w : Fin 8 → ZMod 2) : Prop :=
  w 0 = w 1 ∧ w 2 = w 3 ∧ w 4 = w 5 ∧ w 6 = w 7

private instance (w : Fin 8 → ZMod 2) : Decidable (pairConstant w) :=
  inferInstanceAs (Decidable (w 0 = w 1 ∧ w 2 = w 3 ∧ w 4 = w 5 ∧ w 6 = w 7))

private theorem pairConstant_iff (w : Fin 8 → ZMod 2) : pairConstant w ↔
    ∀ i j : Fin 8, i.val / 2 = j.val / 2 → w i = w j := by
  constructor
  · intro h i j hij
    fin_cases i <;> fin_cases j <;> simp_all [pairConstant]
  · intro h
    exact ⟨h 0 1 rfl, h 2 3 rfl, h 4 5 rfl, h 6 7 rfl⟩

private theorem raw_pencil_test : ∀ w : Fin 8 → ZMod 2,
    (∃ a b c : ZMod 2,
      c • DeletedEight.oneWord.val = a • firstWord.val + b • secondWord.val - w) ↔
      pairConstant w ∧ HalfWeight.binaryHalfWeight w = 0 := by
  decide +kernel

private theorem mk_mem_deletedPencil (w : DeletedEight.evenCode) :
    (Submodule.Quotient.mk w : DeletedEight.W) ∈ deletedPencil ↔
      pairConstant w.val ∧ HalfWeight.binaryHalfWeight w.val = 0 := by
  rw [deletedPencil, Submodule.mem_span_pair]
  change (∃ a b : ZMod 2,
    (Submodule.Quotient.mk (a • firstWord + b • secondWord) : DeletedEight.W) =
      Submodule.Quotient.mk w) ↔ _
  simp only [Submodule.Quotient.eq, DeletedEight.constants, Submodule.mem_span_singleton,
    Subtype.ext_iff]
  exact raw_pencil_test w.val

private theorem pairConstant_evenPerm (p : Equiv.Perm (Fin 8)) (hp : p ∈ pairStabilizer)
    (w : DeletedEight.evenCode) (hw : pairConstant w.val) :
    pairConstant (DeletedEight.evenPerm p w).val := by
  rw [pairConstant_iff] at hw ⊢
  intro i j hij
  exact hw _ _ ((mem_pairStabilizer p⁻¹).mp (pairStabilizer.inv_mem hp) i j |>.mpr hij)

private theorem word_pair_test (i j : Fin 8) :
    i.val / 2 = j.val / 2 ↔
      firstWord.val i = firstWord.val j ∧ secondWord.val i = secondWord.val j := by
  have h : ∀ i j : Fin 8, i.val / 2 = j.val / 2 ↔
      firstWord.val i = firstWord.val j ∧ secondWord.val i = secondWord.val j := by
    decide +kernel
  exact h i j

private theorem pair_preimage_of_deleted (p : Equiv.Perm (Fin 8))
    (h : DeletedEight.quotientPerm p ∈ BinaryLinear.parabolic deletedPencil)
    (i j : Fin 8) (hij : i.val / 2 = j.val / 2) :
    (p.symm i).val / 2 = (p.symm j).val / 2 := by
  have maps (w : DeletedEight.evenCode)
      (hw : (Submodule.Quotient.mk w : DeletedEight.W) ∈ deletedPencil) :
      pairConstant (DeletedEight.evenPerm p w).val :=
    ((mk_mem_deletedPencil _).mp ((h _).mpr hw)).1
  apply (word_pair_test _ _).mpr
  exact ⟨(pairConstant_iff _).mp
      (maps firstWord (Submodule.subset_span (by simp))) i j hij,
    (pairConstant_iff _).mp
      (maps secondWord (Submodule.subset_span (by simp))) i j hij⟩

theorem deleted_parabolic_iff (p : Equiv.Perm (Fin 8)) :
    DeletedEight.quotientPerm p ∈ BinaryLinear.parabolic deletedPencil ↔
      p ∈ pairStabilizer := by
  constructor
  · intro h
    have hi : DeletedEight.quotientPerm p⁻¹ ∈ BinaryLinear.parabolic deletedPencil :=
      (BinaryLinear.parabolic deletedPencil).inv_mem h
    apply (mem_pairStabilizer p).mpr
    intro i j
    constructor
    · intro hij
      simpa using pair_preimage_of_deleted p h (p i) (p j) hij
    · exact pair_preimage_of_deleted p⁻¹ hi i j
  · intro hp
    let : Finite DeletedEight.W :=
      Finite.of_equiv DeletedEight.D DeletedEight.splitEquiv.toEquiv
    rw [mem_parabolic_maps]
    intro q hq
    induction q using Submodule.Quotient.induction_on with
    | H w =>
      have hw := (mk_mem_deletedPencil w).mp hq
      apply (mk_mem_deletedPencil _).mpr
      exact ⟨pairConstant_evenPerm p hp w hw.1,
        (DeletedEight.evenPerm_halfWeight p w).trans hw.2⟩

end
end Theory.SpecificGroups.SymmetricEight.PairFlagParabolic
