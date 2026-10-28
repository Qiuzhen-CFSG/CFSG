module

public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Normal subgroups of SL(2) avoiding the central involution

Over a finite field of odd characteristic, every nontrivial normal subgroup of
`SL(2, F)` contains `-1`. This is the normal-subgroup fact used when extracting
a faithful irreducible constituent in ABG, Section II.4, Lemma 18 (article p.45).

For fields with at least four elements, simplicity of `PSL(2, F)` makes the
image of a normal subgroup trivial or surjective. A trivial image lies in
the center `{1, -1}`. A surjective image contains a lift of the projective
image of `[[0, -1], [1, 0]]`; either lift squares to `-1`.

For the exceptional field of three elements, a finite certificate shows that
each nonidentity matrix, or its product with one of two specified conjugates,
has a power equal to `-1`. The certificate is checked by kernel reduction and
transported along the field isomorphism with `ZMod 3`.
-/

open Matrix
open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

private lemma center_rank_two {F : Type*} [Field F] {g : SL(2, F)}
    (hg : g ∈ Subgroup.center SL(2, F)) : g = 1 ∨ g = -1 := by
  obtain ⟨a, ha, h⟩ := mem_center_iff.mp hg
  simp only [Fintype.card_fin] at ha
  rcases sq_eq_one_iff.mp ha with rfl | rfl
  · left
    apply Subtype.ext
    simpa using h.symm
  · right
    apply Subtype.ext
    simpa [← Matrix.diagonal_neg] using h.symm

private def sqrtNegOne (F : Type*) [Field F] : SL(2, F) :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩

private lemma sqrtNegOne_sq (F : Type*) [Field F] : sqrtNegOne F ^ 2 = -1 := by
  apply Subtype.ext
  change (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) ^ 2 = -1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]

private lemma eq_bot_of_four_le_card {F : Type*} [Field F] (hF : 4 ≤ Nat.card F)
    (N : Subgroup SL(2, F)) [N.Normal] (hN : (-1 : SL(2, F)) ∉ N) : N = ⊥ := by
  let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := F) hF
  let f := QuotientGroup.mk' (Subgroup.center SL(2, F))
  rcases (inferInstance : (N.map f).Normal).eq_bot_or_eq_top with hbot | htop
  · apply N.eq_bot_iff_forall.mpr
    intro g hg
    have hc : g ∈ Subgroup.center SL(2, F) := by
      have := (N.map_eq_bot_iff.mp hbot) hg
      simpa [f] using this
    rcases center_rank_two hc with h | h
    · exact h
    · exact False.elim (hN (h ▸ hg))
  · have hs : f (sqrtNegOne F) ∈ N.map f := by rw [htop]; trivial
    obtain ⟨g, hg, heq⟩ := hs
    have hc : g⁻¹ * sqrtNegOne F ∈ Subgroup.center SL(2, F) :=
      QuotientGroup.eq.mp heq
    rcases center_rank_two hc with h | h
    · have hgs : g = sqrtNegOne F := inv_mul_eq_one.mp h
      exact False.elim (hN (sqrtNegOne_sq F ▸ (hgs ▸ N.pow_mem hg 2)))
    · have hs : sqrtNegOne F = g * (-1) := inv_mul_eq_iff_eq_mul.mp h
      have hsq : g ^ 2 = -1 := by simpa [hs, pow_two] using sqrtNegOne_sq F
      exact False.elim (hN (hsq ▸ N.pow_mem hg 2))

private def upper : SL(2, ZMod 3) := transvection zero_ne_one 1
private def lower : SL(2, ZMod 3) := transvection one_ne_zero 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private lemma normal_closure_certificate (g : SL(2, ZMod 3)) :
    g = 1 ∨ g ^ 2 = -1 ∨ g ^ 3 = -1 ∨
      (g * (upper * g * upper⁻¹)) ^ 2 = -1 ∨
      (g * (lower * g * lower⁻¹)) ^ 2 = -1 ∨
      (g * (upper * g * upper⁻¹)) ^ 3 = -1 ∨
      (g * (lower * g * lower⁻¹)) ^ 3 = -1 := by
  revert g
  decide +kernel

private lemma eq_bot_over_zmod_three (N : Subgroup SL(2, ZMod 3)) [N.Normal]
    (hN : (-1 : SL(2, ZMod 3)) ∉ N) : N = ⊥ := by
  apply N.eq_bot_iff_forall.mpr
  intro g hg
  have hc (x : SL(2, ZMod 3)) : g * (x * g * x⁻¹) ∈ N :=
    N.mul_mem hg ((inferInstance : N.Normal).conj_mem g hg x)
  rcases normal_closure_certificate g with h | h | h | h | h | h | h
  · exact h
  · exact False.elim (hN (h ▸ N.pow_mem hg 2))
  · exact False.elim (hN (h ▸ N.pow_mem hg 3))
  · exact False.elim (hN (h ▸ N.pow_mem (hc upper) 2))
  · exact False.elim (hN (h ▸ N.pow_mem (hc lower) 2))
  · exact False.elim (hN (h ▸ N.pow_mem (hc upper) 3))
  · exact False.elim (hN (h ▸ N.pow_mem (hc lower) 3))

private lemma eq_bot_of_card_three {F : Type*} [Field F] [Fintype F]
    (hF : Fintype.card F = 3) (N : Subgroup SL(2, F)) [N.Normal]
    (hN : (-1 : SL(2, F)) ∉ N) : N = ⊥ := by
  let e := ZMod.ringEquivOfPrime F (by decide : Nat.Prime 3) hF
  let f : SL(2, ZMod 3) →* SL(2, F) := map e.toRingHom
  have hf : Function.Surjective f := by
    intro g
    refine ⟨map e.symm.toRingHom g, ?_⟩
    ext i j
    exact e.apply_symm_apply (g i j)
  have hfneg : f (-1) = -1 := by
    ext i j
    change e ((-1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) i j) =
      (-1 : Matrix (Fin 2) (Fin 2) F) i j
    simp [Matrix.one_apply]
  have hpre : N.comap f = ⊥ := eq_bot_over_zmod_three _ (by simpa [hfneg] using hN)
  apply N.eq_bot_iff_forall.mpr
  intro g hg
  obtain ⟨x, rfl⟩ := hf g
  have hx : x ∈ N.comap f := hg
  rw [hpre, Subgroup.mem_bot] at hx
  simp [hx]

/-- A normal subgroup of `SL(2, F)` avoiding `-1` is trivial when `F` is a
finite field of odd characteristic, including the field of three elements. -/
public theorem eq_bot_of_neg_one_not_mem {F : Type*} [Field F] [Finite F]
    (hF : (2 : F) ≠ 0) (N : Subgroup SL(2, F)) [N.Normal]
    (hN : (-1 : SL(2, F)) ∉ N) : N = ⊥ := by
  classical
  let := Fintype.ofFinite F
  by_cases hcard : 4 ≤ Nat.card F
  · exact eq_bot_of_four_le_card hcard N hN
  · have hchar : ringChar F ≠ 2 := by
      intro h
      have : CharP F 2 := ringChar.eq_iff.mp h
      exact hF (CharP.cast_eq_zero F 2)
    have hodd := FiniteField.odd_card_of_char_ne_two hchar
    have htwo := Fintype.one_lt_card (α := F)
    have hthree : Fintype.card F = 3 := by
      rw [Nat.card_eq_fintype_card] at hcard
      omega
    exact eq_bot_of_card_three hthree N hN

end Matrix.SpecialLinearGroup
