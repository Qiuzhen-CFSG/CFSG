/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Parts adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
The adapted portions are covered by the ATLAS Research and Attribution
License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Elementary
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants.Spinor.SquareClasses
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.Data.Fin.VecNotation

/-!
# At most four classes modulo the full orthogonal commutator

Conjugacy of equal-value reflections makes their images in the abelianization
identical. Scaling shows that these images depend only on the square class of
the quadratic value. Over a finite odd field there are two square classes;
reflection generation therefore bounds the abelianization by four.

Only representation of nonzero field values is required. In particular one
hyperbolic pair suffices, so the result applies to the minus four-space over F₃.
The proof adapts ATLAS `ReflectionConjugation`, `ReflectionSquareClass`,
`ElementaryQuotientOrder`, and `GroupTheory/TwoInvolutionsBound`, replacing the
Witt-index-two elementary quotient by the literal commutator quotient.
Source: GLS3 §2.7.
-/

@[expose] public noncomputable section

namespace ClassicalOrthogonal.SpinorInvariants
variable {G : Type*} [Group G]

private theorem card_le_four_of_two_commuting_involutions (a b : G) (ha : a*a = 1) (hb : b*b = 1)
    (hab : a*b = b*a) (hgen : Subgroup.closure ({a,b} : Set G) = ⊤) : Nat.card G ≤ 4 := by
  have hab_a : (a*b)*a = b := by rw [mul_assoc, ← hab, ← mul_assoc, ha, one_mul]
  have hab_b : (a*b)*b = a := by rw [mul_assoc, hb, mul_one]
  have ha_ab : a*(a*b) = b := by rw [← mul_assoc, ha, one_mul]
  have hb_ab : b*(a*b) = a := by rw [← mul_assoc, ← hab, hab_b]
  have hab_ab : (a*b)*(a*b) = 1 := by rw [← mul_assoc, hab_a, hb]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have habi : (a*b)⁻¹ = a*b := inv_eq_of_mul_eq_one_right hab_ab
  let S : Subgroup G :=
    { carrier := {x | x=1 ∨ x=a ∨ x=b ∨ x=a*b}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro x y (rfl|rfl|rfl|rfl) (rfl|rfl|rfl|rfl) <;>
          simp only [one_mul, mul_one, ha, hb, hab_a, hab_b, ha_ab, hb_ab, hab_ab,
            ← hab, Set.mem_ofPred_eq] <;> tauto
      inv_mem' := by
        rintro x (rfl|rfl|rfl|rfl) <;>
          simp only [inv_one, hai, hbi, habi, Set.mem_ofPred_eq] <;> tauto }
  have hs : Subgroup.closure ({a,b} : Set G) ≤ S := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact Or.inr (Or.inl rfl)
    · have hx' : x = b := Set.mem_singleton_iff.mp hx
      exact Or.inr (Or.inr (Or.inl hx'))
  rw [hgen] at hs
  let f : Fin 4 → G := ![1,a,b,a*b]
  have hf : Function.Surjective f := by
    intro x
    rcases hs (Subgroup.mem_top x) with h|h|h|h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
    · exact ⟨3, h.symm⟩
  simpa using Nat.card_le_card_of_surjective f hf

end ClassicalOrthogonal.SpinorInvariants

open Theory.AlgebraicGroup
namespace ClassicalOrthogonal.ReflectionGeneration
open ClassicalOrthogonal.Quadratic
universe u
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- Scaling the reflecting vector does not change the reflection. -/
theorem reflectionElement_smul (a : V) (ha : Q a ≠ 0) (c : F) (hc : c ≠ 0) :
    reflectionElement Q (c • a)
      (by rw [Q.map_smul, smul_eq_mul]; exact mul_ne_zero (mul_ne_zero hc hc) ha) =
      reflectionElement Q a ha := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change reflectionLinear Q (c • a)
    (by rw [Q.map_smul, smul_eq_mul]; exact mul_ne_zero (mul_ne_zero hc hc) ha) x =
      reflectionLinear Q a ha x
  rw [reflectionLinear_apply, reflectionLinear_apply, Q.map_smul, map_smul,
    smul_eq_mul, smul_eq_mul, smul_smul]
  congr 1
  congr 1
  field_simp

end ClassicalOrthogonal.ReflectionGeneration

namespace ClassicalOrthogonal.SpinorInvariants
open ClassicalOrthogonal.Quadratic ClassicalOrthogonal.ReflectionGeneration
universe u
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- Equal-value reflections have the same image modulo the full commutator. -/
theorem abelianization_reflection_equal_value (h2 : (2 : F) ≠ 0)
    (a b : V) (ha : Q a ≠ 0) (hb : Q b ≠ 0) (hab : Q a = Q b) :
    Abelianization.of (reflectionElement Q a ha) =
      Abelianization.of (reflectionElement Q b hb) := by
  have hm := equal_value_reflection_product_mem_commutator Q h2 b a hb ha hab.symm
  rw [← Abelianization.ker_of (quadraticIsometrySubgroup Q), MonoidHom.mem_ker,
    map_mul] at hm
  have hs : Abelianization.of (reflectionElement Q b hb) *
      Abelianization.of (reflectionElement Q b hb) = 1 := by
    rw [← map_mul, ← pow_two, reflectionElement_square, map_one]
  exact mul_right_cancel (hm.trans hs.symm)

/-- The image of a reflection in the full abelianization depends only on its value's square class. -/
theorem abelianization_reflection_squareClass (h2 : (2 : F) ≠ 0)
    (a b : V) (ha : Q a ≠ 0) (hb : Q b ≠ 0)
    (hclass : Atlas.squareClass F (Units.mk0 (Q a) ha) =
      Atlas.squareClass F (Units.mk0 (Q b) hb)) :
    Abelianization.of (reflectionElement Q a ha) =
      Abelianization.of (reflectionElement Q b hb) := by
  have hm : Units.mk0 (Q a) ha / Units.mk0 (Q b) hb ∈ Atlas.squareUnits F :=
    QuotientGroup.eq_iff_div_mem.mp hclass
  obtain ⟨c, hc⟩ := hm
  change c ^ 2 = Units.mk0 (Q a) ha / Units.mk0 (Q b) hb at hc
  have hv := congrArg Units.val hc
  simp only [Units.val_pow_eq_pow_val, Units.val_div_eq_div_val, Units.val_mk0] at hv
  have hv' : Q (c.val • b) = Q a := by
    rw [Q.map_smul, smul_eq_mul, ← pow_two, hv, div_mul_cancel₀ _ hb]
  have hcb : Q (c.val • b) ≠ 0 := ne_of_eq_of_ne hv' ha
  have he := abelianization_reflection_equal_value Q h2 a (c.val • b) ha hcb hv'.symm
  rwa [reflectionElement_smul Q b hb c.val c.ne_zero] at he

variable [FiniteDimensional F V]

/-- Two reflection square classes generate the full orthogonal abelianization. -/
theorem card_abelianization_le_four [Finite F]
    (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)
    (hrep : ∀ c : F, c ≠ 0 → ∃ a : V, Q a = c) :
    Nat.card (Abelianization (quadraticIsometrySubgroup Q)) ≤ 4 := by
  have hcard : Nat.card (Atlas.SquareClass F) = 2 := by
    rw [Atlas.card_squareClass, if_neg h2]
  obtain ⟨s, t, _, hcover⟩ := Nat.card_eq_two_iff.mp hcard
  obtain ⟨c, hc⟩ := Atlas.squareClass_surjective F s
  obtain ⟨d, hd⟩ := Atlas.squareClass_surjective F t
  obtain ⟨a, ha⟩ := hrep c.val c.ne_zero
  obtain ⟨b, hb⟩ := hrep d.val d.ne_zero
  have hane : Q a ≠ 0 := ne_of_eq_of_ne ha c.ne_zero
  have hbne : Q b ≠ 0 := ne_of_eq_of_ne hb d.ne_zero
  let r := Abelianization.of (reflectionElement Q a hane)
  let z := Abelianization.of (reflectionElement Q b hbne)
  have hra : Atlas.squareClass F (Units.mk0 (Q a) hane) = s := by
    have he : Units.mk0 (Q a) hane = c := Units.ext ha
    rw [he, hc]
  have hrb : Atlas.squareClass F (Units.mk0 (Q b) hbne) = t := by
    have he : Units.mk0 (Q b) hbne = d := Units.ext hb
    rw [he, hd]
  let S := Subgroup.closure ({r, z} : Set (Abelianization (quadraticIsometrySubgroup Q)))
  have hr : reflectionSubgroup Q ≤ S.comap Abelianization.of := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨v, hv, rfl⟩
    have hm : Atlas.squareClass F (Units.mk0 (Q v) hv) ∈
        ({s, t} : Set (Atlas.SquareClass F)) := by
      rw [hcover]
      trivial
    rcases Set.mem_insert_iff.mp hm with he | he
    · have he' := abelianization_reflection_squareClass Q h2 v a hv hane (he.trans hra.symm)
      change Abelianization.of (reflectionElement Q v hv) ∈ S
      rw [he']
      exact Subgroup.subset_closure (Set.mem_insert r {z})
    · have he := Set.mem_singleton_iff.mp he
      have he' := abelianization_reflection_squareClass Q h2 v b hv hbne (he.trans hrb.symm)
      change Abelianization.of (reflectionElement Q v hv) ∈ S
      rw [he']
      exact Subgroup.subset_closure (Set.mem_insert_of_mem r (Set.mem_singleton z))
  rw [reflectionSubgroup_eq_top Q hQ h2] at hr
  have hgen : S = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (commutator (quadraticIsometrySubgroup Q)) x
    exact hr (Subgroup.mem_top g)
  have hrsq : r * r = 1 := by
    change Abelianization.of (reflectionElement Q a hane) * _ = 1
    rw [← map_mul, ← pow_two, reflectionElement_square, map_one]
  have hzsq : z * z = 1 := by
    change Abelianization.of (reflectionElement Q b hbne) * _ = 1
    rw [← map_mul, ← pow_two, reflectionElement_square, map_one]
  exact card_le_four_of_two_commuting_involutions r z hrsq hzsq (mul_comm r z) hgen

end ClassicalOrthogonal.SpinorInvariants
