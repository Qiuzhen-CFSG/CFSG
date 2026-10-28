/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechAxisShell.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechShortShellCounts

/-!
The forty-eight signed axis vectors of squared norm eight.
Their coordinate parametrization is injective and exhausts the axis shape.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
attribute [local instance] Classical.propDecidable

def eightAxisVector (p : Omega × Bit) : IntegerCoordinates :=
  coordinateVector p.1 (if p.2 = 0 then 8 else -8)

theorem eightAxisVector_injective : Function.Injective eightAxisVector := by
  intro p q h
  have ha : p.1 = q.1 := by
    by_contra hn
    have hi := congrFun h p.1
    simp only [eightAxisVector,coordinateVector,Pi.single_apply] at hi
    split_ifs at hi <;> simp_all
  apply Prod.ext ha
  have hi := congrFun h p.1
  simp only [eightAxisVector,coordinateVector,Pi.single_apply,ha,ite_true] at hi
  rcases bit_cases p.2 with hp | hp <;> rcases bit_cases q.2 with hq | hq <;> simp_all

def axisEightVectors : Finset IntegerCoordinates := Finset.univ.image eightAxisVector

theorem axisEightVectors_card : axisEightVectors.card = 48 := by
  rw [axisEightVectors,Finset.card_image_of_injective _ eightAxisVector_injective]
  simp [Omega,HexIndex,ZMod.card]

theorem eightAxisVector_mem (p : Omega × Bit) : eightAxisVector p ∈ leech := by
  by_cases hp : p.2 = 0
  · simpa [eightAxisVector,hp] using coordinate_eight_mem p.1
  · have hh := leech.neg_mem (coordinate_eight_mem p.1)
    simpa [eightAxisVector,hp,coordinateVector,Pi.single_neg] using hh

theorem eightAxisVector_norm (p : Omega × Bit) :
    integerDot (eightAxisVector p) (eightAxisVector p) = 64 := by
  rw [eightAxisVector,integerDot_coordinateVector]
  simp only [coordinateVector,Pi.single_eq_same]
  split_ifs <;> norm_num

def AxisEightShape (x : IntegerCoordinates) : Prop :=
  (∀ i, x i = -8 ∨ x i = 0 ∨ x i = 8) ∧ (evenMagnitudeSupport x 8).card = 1

theorem eightAxisVector_shape (p : Omega × Bit) : AxisEightShape (eightAxisVector p) := by
  constructor
  · intro i
    simp only [eightAxisVector,coordinateVector,Pi.single_apply]
    split_ifs <;> simp
  · have he : evenMagnitudeSupport (eightAxisVector p) 8 = {p.1} := by
      ext i
      simp only [evenMagnitudeSupport]
      rw [Finset.mem_filter]
      simp only [Finset.mem_univ,true_and,eightAxisVector,coordinateVector,Pi.single_apply,
        Finset.mem_singleton]
      split_ifs <;> simp_all
    rw [he,Finset.card_singleton]

theorem axisEightVectors_iff (x : IntegerCoordinates) : x ∈ axisEightVectors ↔ AxisEightShape x := by
  constructor
  · intro hx
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
    exact eightAxisVector_shape p
  · rintro ⟨hx,hc⟩
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hc
    have haa : x a * x a = 64 := by
      have hm : a ∈ evenMagnitudeSupport x 8 := by rw [ha]; simp
      exact (Finset.mem_filter.mp hm).2
    let b : Bit := if x a = 8 then 0 else 1
    refine Finset.mem_image.mpr ⟨(a,b),Finset.mem_univ _,?_⟩
    funext i
    by_cases hi : i = a
    · subst i
      rcases hx a with h | h | h <;> simp_all [eightAxisVector,coordinateVector,b]
    · have hn : x i * x i ≠ 64 := by
        intro hh
        have hm : i ∈ evenMagnitudeSupport x 8 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩
        rw [ha,Finset.mem_singleton] at hm
        exact hi hm
      rcases hx i with h | h | h <;> simp_all [eightAxisVector,coordinateVector,ne_comm]

end Atlas.Lattices
