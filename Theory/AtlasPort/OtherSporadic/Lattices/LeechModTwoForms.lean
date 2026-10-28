/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechModTwoForms.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechIntegralPairing

/-!
The quadratic and polar functions on the Leech lattice modulo two.
Integral pairing identities prove representative independence and the polarization formula.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes

theorem leechReduction_eq_iff (x y : leech) :
    leechReduction x = leechReduction y ↔ ∃ z : leech, x = y + (2 : ℕ) • z := by
  change (QuotientAddGroup.mk x : LeechModTwo) = QuotientAddGroup.mk y ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem,twiceLeech_mem]
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨z,by rw [hz]; abel⟩
  · rintro ⟨z,hz⟩
    exact ⟨z,by rw [hz]; abel⟩

def leechRepresentative (a : LeechModTwo) : leech := Classical.choose (leechReduction_surjective a)

theorem leechRepresentative_reduce (a : LeechModTwo) : leechReduction (leechRepresentative a) = a :=
  Classical.choose_spec (leechReduction_surjective a)

theorem leechHalfNorm_mod_two_congr (x y : leech) (h : leechReduction x = leechReduction y) :
    (leechHalfNorm x : Bit) = (leechHalfNorm y : Bit) := by
  obtain ⟨z,rfl⟩ := (leechReduction_eq_iff x y).mp h
  rw [leechHalfNorm_add,leechHalfNorm_double,leechIntegralPairing_double_right]
  push_cast
  simp

theorem leechPairing_mod_two_congr_left (x y z : leech) (h : leechReduction x = leechReduction y) :
    (leechIntegralPairing x z : Bit) = (leechIntegralPairing y z : Bit) := by
  obtain ⟨w,rfl⟩ := (leechReduction_eq_iff x y).mp h
  rw [leechIntegralPairing_add_left,leechIntegralPairing_double_left]
  push_cast
  simp

def leechQuadratic (a : LeechModTwo) : Bit := leechHalfNorm (leechRepresentative a)
def leechPolar (a b : LeechModTwo) : Bit :=
  leechIntegralPairing (leechRepresentative a) (leechRepresentative b)

theorem leechQuadratic_reduce (x : leech) : leechQuadratic (leechReduction x) = (leechHalfNorm x : Bit) :=
  leechHalfNorm_mod_two_congr _ _ (leechRepresentative_reduce _)

theorem leechPolar_reduce (x y : leech) :
    leechPolar (leechReduction x) (leechReduction y) = (leechIntegralPairing x y : Bit) := by
  unfold leechPolar
  rw [leechPairing_mod_two_congr_left _ x _ (leechRepresentative_reduce _)]
  rw [leechIntegralPairing_comm x,leechPairing_mod_two_congr_left _ y _ (leechRepresentative_reduce _)]
  rw [leechIntegralPairing_comm]

theorem leechPolar_comm (a b : LeechModTwo) : leechPolar a b = leechPolar b a := by
  simp only [leechPolar,leechIntegralPairing_comm]

theorem leechPolar_add_left (a b c : LeechModTwo) :
    leechPolar (a+b) c = leechPolar a c + leechPolar b c := by
  obtain ⟨x,rfl⟩ := leechReduction_surjective a
  obtain ⟨y,rfl⟩ := leechReduction_surjective b
  obtain ⟨z,rfl⟩ := leechReduction_surjective c
  rw [← map_add,leechPolar_reduce,leechPolar_reduce,leechPolar_reduce,leechIntegralPairing_add_left]
  simp

theorem leechPolar_add_right (a b c : LeechModTwo) :
    leechPolar a (b+c) = leechPolar a b + leechPolar a c := by
  rw [leechPolar_comm a,leechPolar_add_left,leechPolar_comm b,leechPolar_comm c]

theorem leechPolar_self (a : LeechModTwo) : leechPolar a a = 0 := by
  obtain ⟨x,rfl⟩ := leechReduction_surjective a
  rw [leechPolar_reduce,leechIntegralPairing_self]
  simp

theorem leechQuadratic_add (a b : LeechModTwo) :
    leechQuadratic (a+b) = leechQuadratic a + leechQuadratic b + leechPolar a b := by
  obtain ⟨x,rfl⟩ := leechReduction_surjective a
  obtain ⟨y,rfl⟩ := leechReduction_surjective b
  rw [← map_add,leechQuadratic_reduce,leechQuadratic_reduce,leechQuadratic_reduce,
    leechPolar_reduce,leechHalfNorm_add]
  simp

theorem leechQuadratic_zero : leechQuadratic 0 = 0 := by
  have h := leechQuadratic_add 0 0
  rw [add_zero,leechPolar_self,add_zero] at h
  exact (add_eq_left.mp h.symm)

end Atlas.Lattices
