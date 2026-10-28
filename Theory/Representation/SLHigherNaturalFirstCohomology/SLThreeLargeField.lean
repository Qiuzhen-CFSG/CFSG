module

public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary
import Mathlib.Tactic.LinearCombination

/-!
# Natural first cohomology of SL₃ over larger fields

Every cocycle for the actual column-vector action of SL₃(K) is principal when
K is a finite field with more than two elements. In particular its first
cohomology has dimension zero in characteristic two.

The second coordinate of the elementary three-index relation makes the third
coordinate of each transvection value linear in its parameter. Comparing the
first coordinate at (c,c), (c²,1), (1,c), and (c,1) annihilates that third
coordinate by c²(c-1)². Taking c distinct from zero and one gives row support,
and the elementary-generator criterion then gives principality. The calculation
does not require the characteristic-two hypothesis.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(4), printed p.408 (PDF p.419), larger-field branch.
-/

open Matrix Matrix.SpecialLinearGroup

namespace Representation.OneCohomology.SLHigherNatural

variable {K : Type*} [Field K]

private lemma column_zero (f : cocycles (specialLinearNatural (k := K) 3))
    {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a : K) :
    f.val (transvection hij a) j = 0 :=
  cocycle_off_diagonal f hij hjk.symm hjk hij.symm hik.symm a

private lemma chain_second (f : cocycles (specialLinearNatural (k := K) 3))
    {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : K) :
    f.val (transvection hik (a * b)) j + b * f.val (transvection hij a) k = 0 := by
  have hf : ∀ g t, f.val (g * t) = specialLinearNatural 3 g (f.val t) + f.val g :=
    f.property
  have h := congrArg (fun g => f.val g j) (transvection_chain hij hjk hik a b)
  simp only [hf, map_mul, Module.End.mul_apply, action_transvection, Pi.add_apply] at h
  simp [hij.symm, hik.symm, column_zero f hik hjk.symm hij (a * b)] at h
  linear_combination -h

private lemma third_linear (f : cocycles (specialLinearNatural (k := K) 3))
    {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a : K) :
    f.val (transvection hij a) k = a * f.val (transvection hij 1) k := by
  have h₁ := chain_second f hij hjk hik 1 a
  have h₂ := chain_second f hik hjk.symm hij a 1
  simp only [one_mul, mul_one] at h₁ h₂
  linear_combination h₂ - h₁

private lemma chain_first (f : cocycles (specialLinearNatural (k := K) 3))
    {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : K) :
    f.val (transvection hik (a * b)) i =
      a * f.val (transvection hjk b) j - a ^ 2 * b * f.val (transvection hij 1) k := by
  have hf : ∀ g t, f.val (g * t) = specialLinearNatural 3 g (f.val t) + f.val g :=
    f.property
  have h := congrArg (fun g => f.val g i) (transvection_chain hij hjk hik a b)
  simp only [hf, map_mul, Module.End.mul_apply, action_transvection, Pi.add_apply] at h
  simp [hij, third_linear f hij hjk hik a] at h
  linear_combination -h

private lemma third_zero (f : cocycles (specialLinearNatural (k := K) 3))
    (c : K) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a : K) :
    f.val (transvection hij a) k = 0 := by
  have h₁ := chain_first f hij hjk hik c c
  have h₂ := chain_first f hij hjk hik (c * c) 1
  have h₃ := chain_first f hij hjk hik 1 c
  have h₄ := chain_first f hij hjk hik c 1
  simp only [one_mul, mul_one, one_pow] at h₁ h₂ h₃ h₄
  have hz : c * c * (c - 1) * (c - 1) * f.val (transvection hij 1) k = 0 := by
    linear_combination -h₁ + h₂ + c * h₃ - c * h₄
  have ht : f.val (transvection hij 1) k = 0 :=
    (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (mul_ne_zero (mul_ne_zero hc0 hc0)
      (sub_ne_zero.mpr hc1)) (sub_ne_zero.mpr hc1))
  rw [third_linear f hij hjk hik a, ht, mul_zero]

variable [Finite K]

private lemma large_field_element (hK : 2 < Nat.card K) : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  classical
  let := Fintype.ofFinite K
  by_contra! h
  have hs : (Finset.univ : Finset K) ⊆ {0, 1} := by
    intro c _
    by_cases hc : c = 0
    · simp [hc]
    · simp [h c hc]
  have hb := (Finset.card_le_card hs).trans Finset.card_le_two
  exact (not_lt_of_ge hb) (by simpa [Nat.card_eq_fintype_card] using hK)

/-- Elementary cocycle values are supported in their rows over a field of size greater than two. -/
public lemma cocycle_transvection_support_sl3_large_field (hK : 2 < Nat.card K)
    (f : cocycles (specialLinearNatural (k := K) 3))
    {i j : Fin 3} (hij : i ≠ j) (a : K) :
    f.val (transvection hij a) = Pi.single i (f.val (transvection hij a) i) := by
  obtain ⟨c, hc0, hc1⟩ := large_field_element hK
  ext r
  by_cases hri : r = i
  · subst r
    simp
  rw [Pi.single_eq_of_ne hri]
  by_cases hrj : r = j
  · subst r
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide)
    exact column_zero f hij hkj.symm hki.symm a
  · exact third_zero f c hc0 hc1 hij (Ne.symm hrj) (Ne.symm hri) a

/-- Every natural SL₃ cocycle over a finite field of size greater than two is principal. -/
public theorem exists_principal_sl3_large_field (hK : 2 < Nat.card K)
    (f : cocycles (specialLinearNatural (k := K) 3)) :
    ∃ v : Fin 3 → K, f = principal (specialLinearNatural (k := K) 3) v := by
  exact exists_principal_of_support (by decide) f
    (fun _ _ hij a => cocycle_transvection_support_sl3_large_field hK f hij a)

/-- Natural SL₃ first cohomology vanishes over finite fields of size greater than two. -/
public theorem H1_subsingleton_sl3_large_field (hK : 2 < Nat.card K) :
    Subsingleton (H1 (specialLinearNatural (k := K) 3)) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro f _
  obtain ⟨v, hv⟩ := exists_principal_sl3_large_field hK f
  exact ⟨v, hv.symm⟩

/-- The K-dimension of natural SL₃ first cohomology is zero over larger finite fields. -/
public theorem finrank_H1_sl3_large_field (hK : 2 < Nat.card K) :
    Module.finrank K (H1 (specialLinearNatural (k := K) 3)) = 0 := by
  let := H1_subsingleton_sl3_large_field hK
  exact Module.finrank_zero_of_subsingleton

end Representation.OneCohomology.SLHigherNatural
