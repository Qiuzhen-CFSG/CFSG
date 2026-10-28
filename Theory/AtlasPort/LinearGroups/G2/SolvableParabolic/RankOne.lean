module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic

/-!
# Solvable rank-one actions in characteristic two

A subgroup of GL₂ containing every upper transvection either preserves the
first coordinate line or contains SL₂. Indeed, an element with nonzero
lower-left entry can be made anti-diagonal by multiplication by upper
transvections. Conjugating the upper transvections by this element produces
every lower transvection, and the two root groups generate SL₂.

Over a finite field of characteristic two and order greater than two, SL₂ is
nontrivial and perfect. Consequently a solvable action containing all upper
transvections preserves their fixed line. The matrix-homomorphism version is
intended for the plane and plane-quotient actions of the two full G₂ parabolics.

Source context: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528), the characteristic-two paragraph for p = 3. This is an elementary
rank-one ingredient, independent of A.3.15 and of any Borel-containment premise.
-/

@[expose] public section

open Matrix
open scoped MatrixGroups
namespace Atlas.G2.SolvableParabolic.RankOne
variable {F : Type*} [Field F]

/-- The upper transvection, as an invertible matrix. -/
def upper (a : F) : GL (Fin 2) F :=
  SpecialLinearGroup.toGL (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) a)

private def lower (a : F) : GL (Fin 2) F :=
  SpecialLinearGroup.toGL (SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) a)

theorem upper_val (a : F) : (upper a).val = !![1,a;0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper, SpecialLinearGroup.toGL,
    SpecialLinearGroup.transvection_coe]

private theorem lower_val (a : F) : (lower a).val = !![1,0;a,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lower, SpecialLinearGroup.toGL,
    SpecialLinearGroup.transvection_coe]

private theorem specialLinear_le_of_lower_left_ne_zero (H : Subgroup (GL (Fin 2) F))
    (hu : ∀ a, upper a ∈ H) (g : GL (Fin 2) F) (hg : g ∈ H)
    (hc : g 1 0 ≠ 0) : SpecialLinearGroup.toGL.range ≤ H := by
  let k := upper (-g 0 0 / g 1 0) * g * upper (-g 1 1 / g 1 0)
  have hk : k ∈ H := H.mul_mem (H.mul_mem (hu _) hg) (hu _)
  have hk00 : k 0 0 = 0 := by
    simp [k, Units.val_mul, upper_val, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    field_simp [hc]
    ring
  have hk11 : k 1 1 = 0 := by
    simp [k, Units.val_mul, upper_val, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    field_simp [hc]
    ring
  have hk10 : k 1 0 = g 1 0 := by
    simp [k, Units.val_mul, upper_val, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have hl (a : F) : lower a ∈ H := by
    have he : k * upper (a * k 0 1 / g 1 0) = lower a * k := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Units.val_mul, upper_val, lower_val, Matrix.mul_apply,
          Fin.sum_univ_two, hk00, hk11, hk10]
      field_simp [hc]
    have he' : k * upper (a * k 0 1 / g 1 0) * k⁻¹ = lower a := by
      rw [he, mul_inv_cancel_right]
    rw [← he']
    exact H.mul_mem (H.mul_mem hk (hu _)) (H.inv_mem hk)
  rintro _ ⟨M,rfl⟩
  apply Matrix.SL2.transvection_induction (fun M => SpecialLinearGroup.toGL M ∈ H) ?_ ?_ M
  · intro i j hij a
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hu a
    · exact hl a
    · exact (hij rfl).elim
  · intro A B hA hB
    rw [map_mul]
    exact H.mul_mem hA hB

/-- A solvable overgroup of the full upper root group preserves its line. -/
theorem lower_left_eq_zero_of_solvable [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) (H : Subgroup (GL (Fin 2) F)) [Group.IsSolvable H]
    (hu : ∀ a, upper a ∈ H) (g : H) : g.val 1 0 = 0 := by
  classical
  by_contra hc
  have hle := specialLinear_le_of_lower_left_ne_zero H hu g.val g.property hc
  let f : SL(2,F) →* H := SpecialLinearGroup.toGL.codRestrict H
    (fun M => hle ⟨M,rfl⟩)
  let : Group.IsSolvable SL(2,F) := Group.isSolvable_of_isSolvable_injective
    (f := f) (fun a b h => SpecialLinearGroup.toGL_injective (congrArg Subtype.val h))
  let := Fintype.ofFinite F
  have hcard : ({0,1} : Finset F).card < (Finset.univ : Finset F).card := by
    simpa [Nat.card_eq_fintype_card] using hq
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have ha' : a ≠ 0 ∧ a ≠ 1 := by simpa using ha
  have hasq : a^2 ≠ 1 := by
    intro he
    rcases sq_eq_one_iff.mp he with he | he
    · exact ha'.2 he
    · exact ha'.2 (by simpa only [CharTwo.neg_eq] using he)
  let : Group.IsPerfect SL(2,F) := ⟨Matrix.SL2.commutator_eq_top ha'.1 hasq⟩
  let : Nontrivial SL(2,F) := ⟨⟨
    SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (1 : F), 1, by
      intro h
      have he := congrArg (fun M : SL(2,F) => M 0 1) h
      simp [SpecialLinearGroup.transvection_coe] at he⟩⟩
  exact Group.IsPerfect.not_isSolvable SL(2,F) inferInstance

/-- A solvable linear action containing every upper transvection preserves its fixed line. -/
theorem representation_lower_left_eq_zero [Finite F] [CharP F 2]
    {G : Type*} [Group G] [Group.IsSolvable G]
    (hq : 2 < Nat.card F) (ρ : G →* Matrix (Fin 2) (Fin 2) F)
    (hu : ∀ a : F, ∃ g : G, ρ g = !![1,a;0,1]) (g : G) : ρ g 1 0 = 0 := by
  let f := ρ.toHomUnits
  let : Group.IsSolvable f.range :=
    Group.isSolvable_of_surjective f.rangeRestrict_surjective
  apply lower_left_eq_zero_of_solvable hq f.range ?_ ⟨f g, ⟨g,rfl⟩⟩
  intro a
  obtain ⟨x,hx⟩ := hu a
  refine ⟨x, ?_⟩
  apply Units.ext
  change ρ x = (upper a).val
  rw [hx,upper_val]

end Atlas.G2.SolvableParabolic.RankOne
