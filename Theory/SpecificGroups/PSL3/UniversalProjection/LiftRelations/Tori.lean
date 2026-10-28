module

public import Theory.SpecificGroups.PSL3.UniversalProjection.Lifts
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Separating diagonal elements for degree-three roots

For a finite field of order different from two and four, its unit group
contains an element whose cube is not one: otherwise its order divides three.
Put its inverse square at the coordinate outside a chosen root and the unit
itself at the other two coordinates. This gives an actual determinant-one
diagonal matrix. Its projective image fixes the chosen root and scales every
distinct, nonopposite root by a nontrivial cube or inverse cube.

These are the concrete torus elements used to remove central errors from
lifted Steinberg relations. Source: Steinberg, *Lectures on Chevalley Groups*,
Section 7, proof of Theorem 10, steps (5a) and (8), printed pp.82–84;
`refs/KGroup/GLS3/Chapter2St1.tex`. The degree-three cube calculation also
covers the field of order three, which is outside that theorem's general
hypothesis. The resulting ordinary covering is the A₂ case of GLS98 6.1.4.
-/

@[expose] public section

open scoped MatrixGroups commutatorElement
open Theory.SpecificGroups.LinearHigher
namespace Matrix.PSL3.UniversalProjection
variable {F : Type*} [Field F]

/-- A torus can separate distinct, nonopposite roots. -/
def SeparatingTori (F : Type*) [Field F] : Prop :=
  ∀ r s : Root 3, r ≠ s → (r.val.1 ≠ s.val.2 ∨ r.val.2 ≠ s.val.1) →
    ∃ (d : F) (t : PSL(3,F)), d ≠ 1 ∧
      (∀ a, t * projectiveRoot r a * t⁻¹ = projectiveRoot r (d*a)) ∧
      (∀ b, t * projectiveRoot s b * t⁻¹ = projectiveRoot s b)

private theorem exists_noncubic_unit [Finite F] (h2 : Nat.card F ≠ 2)
    (h4 : Nat.card F ≠ 4) : ∃ u : Fˣ, u ^ 3 ≠ 1 := by
  let := Fintype.ofFinite F
  by_contra! h
  have hd := (FiniteField.forall_pow_eq_one_iff F 3).mp h
  have hcard : 2 ≤ Fintype.card F := Fintype.one_lt_card
  rw [Nat.card_eq_fintype_card] at h2 h4
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h | h <;> omega

private def coordinateTorus (m : Fin 3) (u : Fˣ) : SL(3,F) :=
  ⟨Matrix.diagonal (fun l => if l = m then (↑u⁻¹ : F)^2 else (u : F)), by
    fin_cases m <;> simp [Matrix.det_diagonal, Fin.prod_univ_three, pow_two, mul_assoc]⟩

private theorem diagonal_conjugates_root (x : Fin 3 → Fˣ) (t : SL(3,F))
    (ht : t.val = Matrix.diagonal (fun l => (x l : F))) (r : Root 3) (a : F) :
    t * matrixRoot r a * t⁻¹ =
      matrixRoot r (((x r.val.1 : F) * (↑(x r.val.2)⁻¹ : F))*a) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, ht, matrixRoot,
    SpecialLinearGroup.transvection_coe]
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  by_cases hi : i = r.val.1
  · subst i
    by_cases hj : j = r.val.2
    · subst j
      simp [r.property, mul_left_comm, mul_comm]
    · by_cases he : r.val.1 = j <;> simp [hj, he, eq_comm]
  · by_cases he : i = j
    · subst j
      simp [Ne.symm hi]
    · simp [Ne.symm hi, he]

private theorem coordinateTorus_conj (m : Fin 3) (u : Fˣ) (r : Root 3) (a : F) :
    QuotientGroup.mk (coordinateTorus m u) * projectiveRoot r a *
        (QuotientGroup.mk (coordinateTorus m u) : PSL(3,F))⁻¹ =
      projectiveRoot r (((if r.val.1 = m then (↑u⁻¹ : F)^2 else (u : F)) *
        (if r.val.2 = m then (u : F)^2 else (↑u⁻¹ : F)))*a) := by
  have h := diagonal_conjugates_root (fun l => if l = m then u⁻¹^2 else u)
    (coordinateTorus m u) (by
      apply congrArg Matrix.diagonal
      funext l
      split_ifs <;> simp) r a
  have hh := congrArg (QuotientGroup.mk' (Subgroup.center SL(3,F))) h
  simp only [map_mul, map_inv] at hh
  have hcoef : ((↑(if r.val.1 = m then u⁻¹^2 else u) : F) *
      (↑(if r.val.2 = m then u⁻¹^2 else u)⁻¹ : F))*a =
      ((if r.val.1 = m then (↑u⁻¹ : F)^2 else (u : F)) *
        (if r.val.2 = m then (u : F)^2 else (↑u⁻¹ : F)))*a := by
    split_ifs <;> simp
  change _ = projectiveRoot r
    (((↑(if r.val.1 = m then u⁻¹^2 else u) : F) *
      (↑(if r.val.2 = m then u⁻¹^2 else u)⁻¹ : F))*a) at hh
  rw [hcoef] at hh
  exact hh

/-- Diagonal elements separate roots outside the two excluded fields. -/
theorem separatingTori_of_card_ne [Finite F] (h2 : Nat.card F ≠ 2)
    (h4 : Nat.card F ≠ 4) : SeparatingTori F := by
  obtain ⟨u,hu⟩ := exists_noncubic_unit h2 h4
  have hval : (u : F)^3 ≠ 1 := fun h => hu (Units.ext h)
  have hival : (↑u⁻¹ : F)^3 ≠ 1 := by
    intro h
    have hh : (u⁻¹)^3 = 1 := Units.ext h
    exact hu (by simpa only [inv_pow, inv_eq_one] using hh)
  intro r s hrs hnotopp
  let m := auxiliary s
  have hml : m ≠ s.val.1 := auxiliary_ne_left s
  have hmr : m ≠ s.val.2 := auxiliary_ne_right s
  have hne : r.val.1 ≠ s.val.1 ∨ r.val.2 ≠ s.val.2 := by
    by_contra! h
    exact hrs (Subtype.ext (Prod.ext h.1 h.2))
  have hr : r.val.1 = m ∨ r.val.2 = m := by
    have hrr := r.property
    have hss := s.property
    omega
  let t : PSL(3,F) := QuotientGroup.mk (coordinateTorus m u)
  have hs (b : F) : t * projectiveRoot s b * t⁻¹ = projectiveRoot s b := by
    rw [coordinateTorus_conj]
    simp [Ne.symm hml, Ne.symm hmr]
  rcases hr with hl | hr
  · have hr : r.val.2 ≠ m := by rw [← hl]; exact r.property.symm
    refine ⟨(↑u⁻¹ : F)^3, t, hival, ?_, hs⟩
    intro a
    rw [coordinateTorus_conj]
    simp [hl, hr, pow_succ]
  · have hl : r.val.1 ≠ m := by rw [← hr]; exact r.property
    refine ⟨(u : F)^3, t, hval, ?_, hs⟩
    intro a
    rw [coordinateTorus_conj]
    simp [hl, hr, pow_succ, mul_assoc]

end Matrix.PSL3.UniversalProjection
