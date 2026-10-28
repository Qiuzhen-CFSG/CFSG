module

public import Theory.Representation.OrthogonalFourPlusMatrix.Binary
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Canonical pointwise stabilizers in determinant space

The determinant isometries fixing the fixed space of `(u,1)` or `(1,u)`
pointwise are determined by one field coefficient. For `(u,u)`, polarization
of the determinant gives one field coefficient and one binary choice. The
second choice has a one-dimensional displacement image. Excluding rank-one
operators therefore leaves at most four isometries in all three cases.

The proof uses the four matrix units and the literal upper transvection;
it requires no enumeration of a general linear or orthogonal group.
Source application: the near-offender calculation in Aschbacher--Smith,
*The Classification of Quasithin Groups*, combined manuscript of 1 March
2004, H.1.1, printed p.378, used in the field-four tensor branch of 9.2.1.
-/

@[expose] public noncomputable section
open Matrix Module
namespace ClassicalOrthogonal.FourPlusMatrix.Binary

private def E (i j : Fin 2) : V := Matrix.single i j 1

@[simp] private lemma E_apply (i j k l : Fin 2) :
    E i j k l = if i = k ∧ j = l then 1 else 0 := rfl

private def polar (M N : V) : F :=
  M 0 0 * N 1 1 + M 1 1 * N 0 0 - M 0 1 * N 1 0 - M 1 0 * N 0 1

private lemma polar_preserved (t : V ≃ₗ[F] V) (ht : ∀ M, (t M).det = M.det)
    (M N : V) : polar (t M) (t N) = polar M N := by
  have h := ht (M + N)
  have hM := ht M
  have hN := ht N
  simp only [map_add, det_fin_two, Matrix.add_apply] at h hM hN
  unfold polar
  linear_combination h - hM - hN

private lemma map_matrix (t : V ≃ₗ[F] V) (M : V) :
    t M = M 0 0 • t (E 0 0) + M 0 1 • t (E 0 1) +
      M 1 0 • t (E 1 0) + M 1 1 • t (E 1 1) := by
  have hM : M = M 0 0 • E 0 0 + M 0 1 • E 0 1 +
      M 1 0 • E 1 0 + M 1 1 • E 1 1 := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [E_apply]
  conv_lhs => rw [hM]
  simp only [map_add, map_smul]

private lemma left_shape (t : V ≃ₗ[F] V) (ht : ∀ M, (t M).det = M.det)
    (h00 : t (E 0 0) = E 0 0) (h01 : t (E 0 1) = E 0 1) :
    t (E 1 0) = !![(t (E 1 0)) 0 0, 0; 1, 0] ∧
    t (E 1 1) = !![0, (t (E 1 0)) 0 0; 0, 1] := by
  have hp := polar_preserved t ht
  have h1011 : t (E 1 0) 1 1 = 0 := by
    simpa [h00, polar] using hp (E 0 0) (E 1 0)
  have h1010 : t (E 1 0) 1 0 = 1 := by
    simpa [h01, polar] using hp (E 0 1) (E 1 0)
  have h1111 : t (E 1 1) 1 1 = 1 := by
    simpa [h00, polar] using hp (E 0 0) (E 1 1)
  have h1110 : t (E 1 1) 1 0 = 0 := by
    simpa [h01, polar] using hp (E 0 1) (E 1 1)
  have h1001 : t (E 1 0) 0 1 = 0 := by
    simpa [det_fin_two, h1010, h1011] using ht (E 1 0)
  have h1100 : t (E 1 1) 0 0 = 0 := by
    simpa [det_fin_two, h1110, h1111] using ht (E 1 1)
  have hb : t (E 1 1) 0 1 = t (E 1 0) 0 0 := by
    have h := hp (E 1 0) (E 1 1)
    symm
    simpa [polar, h1111, h1110, h1011, h1010,
      sub_eq_zero] using h
  constructor <;> funext i j <;> fin_cases i <;> fin_cases j <;>
    simp [h1011, h1010, h1001, h1111, h1110, h1100, hb]

private lemma right_shape (t : V ≃ₗ[F] V) (ht : ∀ M, (t M).det = M.det)
    (h01 : t (E 0 1) = E 0 1) (h11 : t (E 1 1) = E 1 1) :
    t (E 0 0) = !![1, (t (E 0 0)) 0 1; 0, 0] ∧
    t (E 1 0) = !![0, 0; 1, (t (E 0 0)) 0 1] := by
  have hp := polar_preserved t ht
  have h0010 : t (E 0 0) 1 0 = 0 := by
    simpa [h01, polar] using hp (E 0 1) (E 0 0)
  have h0000 : t (E 0 0) 0 0 = 1 := by
    simpa [h11, polar] using hp (E 1 1) (E 0 0)
  have h1010 : t (E 1 0) 1 0 = 1 := by
    simpa [h01, polar] using hp (E 0 1) (E 1 0)
  have h1000 : t (E 1 0) 0 0 = 0 := by
    simpa [h11, polar] using hp (E 1 1) (E 1 0)
  have h0011 : t (E 0 0) 1 1 = 0 := by
    simpa [det_fin_two, h0010, h0000] using ht (E 0 0)
  have h1001 : t (E 1 0) 0 1 = 0 := by
    simpa [det_fin_two, h1010, h1000] using ht (E 1 0)
  have hb : t (E 1 0) 1 1 = t (E 0 0) 0 1 := by
    simpa [polar, h0000, h0010, h0011, h1010, sub_eq_zero]
      using hp (E 0 0) (E 1 0)
  constructor <;> funext i j <;> fin_cases i <;> fin_cases j <;>
    simp [h0010, h0000, h0011, h1010, h1000, h1001, hb]

private lemma diagonal_shape (t : V ≃ₗ[F] V) (ht : ∀ M, (t M).det = M.det)
    (hI : t (1 : V) = 1) (hN : t (E 0 1) = E 0 1) :
    ∃ a b : F, (a = 0 ∨ a = 1) ∧
      t (E 1 1) = !![a, b; 0, a + 1] ∧
      t (E 1 0) = !![b, b ^ 2; 1, b] := by
  have hp := polar_preserved t ht
  have hD10 : t (E 1 1) 1 0 = 0 := by
    simpa [hN, polar] using hp (E 0 1) (E 1 1)
  have hD11 : t (E 1 1) 1 1 = t (E 1 1) 0 0 + 1 := by
    have h := hp 1 (E 1 1)
    simp only [hI, polar, Matrix.one_apply, E_apply] at h
    norm_num at h
    simpa only [sub_eq_add_neg, CharTwo.neg_eq, add_comm] using eq_sub_of_add_eq h
  have ha : t (E 1 1) 0 0 = 0 ∨ t (E 1 1) 0 0 = 1 := by
    have h := ht (E 1 1)
    simp [det_fin_two, hD10, hD11] at h
    rcases h with h | h
    · exact Or.inl h
    · right
      have := eq_neg_of_add_eq_zero_left h
      simpa only [CharTwo.neg_eq] using this
  have hC10 : t (E 1 0) 1 0 = 1 := by
    simpa [hN, polar] using hp (E 0 1) (E 1 0)
  have hC11 : t (E 1 0) 1 1 = t (E 1 0) 0 0 := by
    have h := hp 1 (E 1 0)
    simpa [hI, polar, CharTwo.add_eq_zero] using h
  have hC01 : t (E 1 0) 0 1 = t (E 1 0) 0 0 ^ 2 := by
    have h := ht (E 1 0)
    symm
    simpa [det_fin_two, hC10, hC11, ← pow_two, sub_eq_zero]
      using h
  have hD01 : t (E 1 1) 0 1 = t (E 1 0) 0 0 := by
    have h := hp (E 1 1) (E 1 0)
    simp only [polar, E_apply, hD10, hD11, hC10, hC11] at h
    norm_num at h
    rw [add_mul, one_mul, ← add_assoc, CharTwo.add_self_eq_zero, zero_add] at h
    exact (sub_eq_zero.mp h).symm
  refine ⟨t (E 1 1) 0 0, t (E 1 0) 0 0, ha, ?_, ?_⟩ <;>
    funext i j <;> fin_cases i <;> fin_cases j <;>
      simp [hD10, hD11, hD01, hC10, hC11, hC01]


/-- The standard nontrivial upper transvection. -/
def canonicalRoot : Matrix.SpecialLinearGroup (Fin 2) F :=
  SpecialLinearGroup.transvection zero_ne_one (1 : F)

theorem canonicalRoot_square : canonicalRoot * canonicalRoot = 1 := by
  rw [canonicalRoot, ← SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
    SpecialLinearGroup.transvection_coeff_zero]

theorem canonicalRoot_ne_one : canonicalRoot ≠ 1 := by
  intro h
  have hh := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => g.val 0 1) h
  simp [canonicalRoot, SpecialLinearGroup.transvection_coe] at hh

private lemma canonicalRoot_inv : canonicalRoot⁻¹ = canonicalRoot :=
  inv_eq_of_mul_eq_one_left canonicalRoot_square

private lemma left_fixed :
    matrixAction (canonicalRoot, (1 : Matrix.SpecialLinearGroup (Fin 2) F)) (E 0 0) = E 0 0 ∧
    matrixAction (canonicalRoot, (1 : Matrix.SpecialLinearGroup (Fin 2) F)) (E 0 1) = E 0 1 := by
  constructor <;> funext i j <;> fin_cases i <;> fin_cases j <;>
    simp [matrixAction, canonicalRoot, SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply]

private lemma right_fixed :
    matrixAction ((1 : Matrix.SpecialLinearGroup (Fin 2) F), canonicalRoot) (E 0 1) = E 0 1 ∧
    matrixAction ((1 : Matrix.SpecialLinearGroup (Fin 2) F), canonicalRoot) (E 1 1) = E 1 1 := by
  constructor
  · change (1 : Matrix.SpecialLinearGroup (Fin 2) F).val * E 0 1 * canonicalRoot⁻¹.val = E 0 1
    rw [canonicalRoot_inv]
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [canonicalRoot, SpecialLinearGroup.transvection_coe, Matrix.mul_apply]
  · change (1 : Matrix.SpecialLinearGroup (Fin 2) F).val * E 1 1 * canonicalRoot⁻¹.val = E 1 1
    rw [canonicalRoot_inv]
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [canonicalRoot, SpecialLinearGroup.transvection_coe, Matrix.mul_apply]

private lemma diagonal_fixed :
    matrixAction (canonicalRoot, canonicalRoot) (1 : V) = 1 ∧
    matrixAction (canonicalRoot, canonicalRoot) (E 0 1) = E 0 1 := by
  constructor
  · change canonicalRoot.val * (1 : V) * canonicalRoot⁻¹.val = 1
    rw [mul_one, ← SpecialLinearGroup.coe_mul, mul_inv_cancel,
      SpecialLinearGroup.coe_one]
  · change canonicalRoot.val * E 0 1 * canonicalRoot⁻¹.val = E 0 1
    rw [canonicalRoot_inv]
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [canonicalRoot, SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
        Fin.sum_univ_two]

private lemma diagonal_first_unit (t : V ≃ₗ[F] V) (hI : t (1 : V) = 1) :
    t (E 0 0) = 1 - t (E 1 1) := by
  have he : E 0 0 = (1 : V) - E 1 1 := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [he, map_sub, hI]

private lemma diagonal_rank_one (t : V ≃ₗ[F] V) (b : F)
    (hI : t (1 : V) = 1) (hN : t (E 0 1) = E 0 1)
    (hD : t (E 1 1) = !![1, b; 0, 0])
    (hC : t (E 1 0) = !![b, b ^ 2; 1, b]) :
    finrank F (LinearMap.range (t.toLinearMap - LinearMap.id)) = 1 := by
  let v : V := !![1, b; 0, 1]
  have hd (M : V) : t M - M = (M 0 0 + M 1 1 + b * M 1 0) • v := by
    rw [map_matrix t M, diagonal_first_unit t hI, hN, hD, hC]
    funext i j
    fin_cases i <;> fin_cases j <;> simp [v, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, sub_eq_add_neg, CharTwo.neg_eq, CharTwo.add_self_eq_zero]
    all_goals ring_nf
    all_goals simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
  have hspan : LinearMap.range (t.toLinearMap - LinearMap.id) = Submodule.span F {v} := by
    apply le_antisymm
    · rintro w ⟨M, rfl⟩
      apply Submodule.mem_span_singleton.mpr
      exact ⟨M 0 0 + M 1 1 + b * M 1 0, (hd M).symm⟩
    · apply Submodule.span_le.mpr
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst w
      refine ⟨E 1 1, ?_⟩
      change t (E 1 1) - E 1 1 = v
      simpa using hd (E 1 1)
  rw [hspan]
  apply finrank_span_singleton
  intro h
  have hh := congrArg (fun M : V => M 0 0) h
  simp [v] at hh

private lemma card_left (A : Subgroup (V ≃ₗ[F] V))
    (hdet : ∀ a ∈ A, ∀ M, (a M).det = M.det)
    (h00 : ∀ a ∈ A, a (E 0 0) = E 0 0)
    (h01 : ∀ a ∈ A, a (E 0 1) = E 0 1) : Nat.card A ≤ 4 := by
  have hi : Function.Injective (fun a : A => (a.val (E 1 0)) 0 0) := by
    intro a b hab
    dsimp only at hab
    apply Subtype.ext
    apply LinearEquiv.ext
    intro M
    obtain ⟨haC, haD⟩ := left_shape a.val (hdet a.val a.property)
      (h00 a.val a.property) (h01 a.val a.property)
    obtain ⟨hbC, hbD⟩ := left_shape b.val (hdet b.val b.property)
      (h00 b.val b.property) (h01 b.val b.property)
    rw [map_matrix a.val M, map_matrix b.val M, h00 a.val a.property,
      h00 b.val b.property, h01 a.val a.property, h01 b.val b.property,
      haC, haD, hbC, hbD, hab]
  simpa only [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_field]
    using Nat.card_le_card_of_injective _ hi

private lemma card_right (A : Subgroup (V ≃ₗ[F] V))
    (hdet : ∀ a ∈ A, ∀ M, (a M).det = M.det)
    (h01 : ∀ a ∈ A, a (E 0 1) = E 0 1)
    (h11 : ∀ a ∈ A, a (E 1 1) = E 1 1) : Nat.card A ≤ 4 := by
  have hi : Function.Injective (fun a : A => (a.val (E 0 0)) 0 1) := by
    intro a b hab
    dsimp only at hab
    apply Subtype.ext
    apply LinearEquiv.ext
    intro M
    obtain ⟨haB, haC⟩ := right_shape a.val (hdet a.val a.property)
      (h01 a.val a.property) (h11 a.val a.property)
    obtain ⟨hbB, hbC⟩ := right_shape b.val (hdet b.val b.property)
      (h01 b.val b.property) (h11 b.val b.property)
    rw [map_matrix a.val M, map_matrix b.val M, h01 a.val a.property,
      h01 b.val b.property, h11 a.val a.property, h11 b.val b.property,
      haB, haC, hbB, hbC, hab]
  simpa only [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_field]
    using Nat.card_le_card_of_injective _ hi

private lemma card_diagonal (A : Subgroup (V ≃ₗ[F] V))
    (hdet : ∀ a ∈ A, ∀ M, (a M).det = M.det)
    (hI : ∀ a ∈ A, a (1 : V) = 1)
    (hN : ∀ a ∈ A, a (E 0 1) = E 0 1)
    (hno : ∀ a ∈ A, a ≠ 1 →
      finrank F (LinearMap.range (a.toLinearMap - LinearMap.id)) ≠ 1) : Nat.card A ≤ 4 := by
  have hshape (t : A) : ∃ b : F,
      t.val (E 1 1) = !![0, b; 0, 1] ∧ t.val (E 1 0) = !![b, b ^ 2; 1, b] := by
    obtain ⟨a, b, ha, hD, hC⟩ := diagonal_shape t.val (hdet t.val t.property)
      (hI t.val t.property) (hN t.val t.property)
    rcases ha with rfl | rfl
    · exact ⟨b, by simpa using hD, hC⟩
    · have hr := diagonal_rank_one t.val b (hI t.val t.property)
        (hN t.val t.property) (by simpa only [CharTwo.add_self_eq_zero] using hD) hC
      have ht : t.val ≠ 1 := by
        intro he
        have hh := congrArg (fun M : V => M 0 0) hD
        simp [he] at hh
      exact (hno t.val t.property ht hr).elim
  have hi : Function.Injective (fun a : A => (a.val (E 1 0)) 0 0) := by
    intro a b hab
    dsimp only at hab
    apply Subtype.ext
    apply LinearEquiv.ext
    intro M
    obtain ⟨x, haD, haC⟩ := hshape a
    obtain ⟨y, hbD, hbC⟩ := hshape b
    have hxy : x = y := by simpa [haC, hbC] using hab
    rw [map_matrix a.val M, map_matrix b.val M,
      diagonal_first_unit a.val (hI a.val a.property),
      diagonal_first_unit b.val (hI b.val b.property),
      hN a.val a.property, hN b.val b.property, haD, haC, hbD, hbC, hxy]
  simpa only [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_field]
    using Nat.card_le_card_of_injective _ hi

/-- A determinant-isometry group fixing a canonical involution's fixed space
pointwise has order at most four if it has no rank-one displacement. -/
theorem canonical_pointwise_card_le_four (r : G)
    (hfst : r.1 = 1 ∨ r.1 = canonicalRoot)
    (hsnd : r.2 = 1 ∨ r.2 = canonicalRoot) (hr : r ≠ 1)
    (A : Subgroup (V ≃ₗ[F] V))
    (hfix : ∀ a ∈ A, ∀ v, matrixAction r v = v → a v = v)
    (hdet : ∀ a ∈ A, ∀ v, (a v).det = v.det)
    (hno : ∀ a ∈ A, a ≠ 1 →
      finrank F (LinearMap.range (a.toLinearMap - LinearMap.id)) ≠ 1) : Nat.card A ≤ 4 := by
  rcases r with ⟨r₁, r₂⟩
  dsimp only at hfst hsnd
  rcases hfst with hfst | hfst <;> rcases hsnd with hsnd | hsnd
  · exact (hr (Prod.ext hfst hsnd)).elim
  · subst r₁; subst r₂
    exact card_right A hdet (fun a ha => hfix a ha _ right_fixed.1)
      (fun a ha => hfix a ha _ right_fixed.2)
  · subst r₁; subst r₂
    exact card_left A hdet (fun a ha => hfix a ha _ left_fixed.1)
      (fun a ha => hfix a ha _ left_fixed.2)
  · subst r₁; subst r₂
    exact card_diagonal A hdet (fun a ha => hfix a ha _ diagonal_fixed.1)
      (fun a ha => hfix a ha _ diagonal_fixed.2) hno

end ClassicalOrthogonal.FourPlusMatrix.Binary
