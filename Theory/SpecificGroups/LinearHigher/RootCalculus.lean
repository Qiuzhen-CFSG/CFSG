module

public import Theory.SpecificGroups.LinearHigher.Presentation

/-!
# Weyl and torus words in the elementary presentation

The additive and three-index commutator relations determine conjugation by
`wᵢⱼ(t) = xᵢⱼ(t) xⱼᵢ(-t⁻¹) xᵢⱼ(t)` and `hᵢⱼ(t) = wᵢⱼ(t) wᵢⱼ(-1)`.
The opposite-root calculation expresses that root as a commutator through
a third coordinate; no additional rank-one relation is assumed.

All formulas hold in any realization of `Relations`, over an arbitrary field.
They supply the local calculations for both the Bruhat reduction and the
finite-field torus relations in the degree-three faithfulness argument.

Source: Steinberg, *Lectures on Chevalley Groups*, §6, Lemma 37, printed
pp.69–70; `refs/KGroup/GLS3/Chapter2St1.tex`.
-/

@[expose] public section

namespace Theory.SpecificGroups.LinearHigher
open scoped commutatorElement

variable {n : ℕ} {F E : Type*} [Field F] [Group E]

namespace Relations
variable {x : Root n → F → E} (h : Relations x)
include h

theorem zero (r : Root n) : x r 0 = 1 := by
  have he := h.add r 0 0
  simpa only [add_zero, mul_eq_left] using he

theorem neg (r : Root n) (a : F) : x r (-a) = (x r a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [h.add, neg_add_cancel, h.zero]

theorem commute (r s : Root n) (a b : F)
    (hrs : r.val.2 ≠ s.val.1) (hsr : s.val.2 ≠ r.val.1) :
    Commute (x r a) (x s b) :=
  commutatorElement_eq_one_iff_commute.mp (h.distant r s a b hrs hsr)

theorem conj_distant (r s : Root n) (a b : F)
    (hrs : r.val.2 ≠ s.val.1) (hsr : s.val.2 ≠ r.val.1) :
    MulAut.conj (x r a) (x s b) = x s b := by
  rw [conj_eq_commutatorElement_mul, h.distant r s a b hrs hsr, one_mul]

theorem conj_chain (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : F) :
    MulAut.conj (x (root i j hij) a) (x (root j k hjk) b) =
      x (root i k hik) (a * b) * x (root j k hjk) b := by
  rw [conj_eq_commutatorElement_mul, h.chain i j k hij hjk hik]

theorem conj_chain_reverse (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : F) :
    MulAut.conj (x (root j k hjk) b) (x (root i j hij) a) =
      x (root i k hik) (-(a * b)) * x (root i j hij) a := by
  rw [conj_eq_commutatorElement_mul, ← commutatorElement_inv,
    h.chain i j k hij hjk hik, ← h.neg]
end Relations

namespace SteinbergWords

def weylWord (x : Root n → F → E) (i j : Fin n) (hij : i ≠ j) (t : Fˣ) : E :=
  x (root i j hij) t * x (root j i hij.symm) (-(t⁻¹ : Fˣ) : F) * x (root i j hij) t

def torusWord (x : Root n → F → E) (i j : Fin n) (hij : i ≠ j) (t : Fˣ) : E :=
  weylWord x i j hij t * weylWord x i j hij (-1)

private theorem conj_mul_apply (a b c : E) :
    MulAut.conj (a * b) c = MulAut.conj a (MulAut.conj b c) := by
  simp only [MulAut.conj_apply, mul_inv_rev, mul_assoc]

variable {x : Root n → F → E} (h : Relations x)
include h

theorem weylWord_inv (i j : Fin n) (hij : i ≠ j) (t : Fˣ) :
    (weylWord x i j hij t)⁻¹ = weylWord x i j hij (-t) := by
  simp [weylWord, mul_inv_rev, ← h.neg, mul_assoc]

@[simp] theorem torusWord_one (i j : Fin n) (hij : i ≠ j) :
    torusWord x i j hij 1 = 1 := by
  rw [torusWord, ← weylWord_inv h, mul_inv_cancel]

theorem weylWord_conj_outgoing (i j k : Fin n) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (t : Fˣ) (a : F) :
    MulAut.conj (weylWord x i j hij t) (x (root i k hik) a) =
      x (root j k hjk) (-((t⁻¹ : Fˣ) : F) * a) := by
  rw [weylWord, conj_mul_apply, conj_mul_apply,
    h.conj_distant (root i j hij) (root i k hik) _ _ hij.symm hik.symm,
    h.conj_chain j i k hij.symm hik hjk, map_mul,
    h.conj_chain i j k hij hjk hik,
    h.conj_distant (root i j hij) (root i k hik) _ _ hij.symm hik.symm]
  rw [mul_assoc, (h.commute (root j k hjk) (root i k hik) _ _ hik.symm hjk.symm).eq,
    ← mul_assoc, h.add]
  have he : (t : F) * (-((t⁻¹ : Fˣ) : F) * a) + a = 0 := by
    simp
  rw [he, h.zero, one_mul]

theorem weylWord_conj_incoming (i j k : Fin n) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (t : Fˣ) (a : F) :
    MulAut.conj (weylWord x i j hij t) (x (root k j hkj) a) =
      x (root k i hki) (a * ((t⁻¹ : Fˣ) : F)) := by
  rw [weylWord, conj_mul_apply, conj_mul_apply,
    h.conj_distant (root i j hij) (root k j hkj) _ _ hkj.symm hij.symm,
    h.conj_chain_reverse k j i hkj hij.symm hki, map_mul,
    h.conj_chain_reverse k i j hki hij hkj,
    h.conj_distant (root i j hij) (root k j hkj) _ _ hkj.symm hij.symm]
  rw [mul_assoc, (h.commute (root k i hki) (root k j hkj) _ _ hki.symm hkj.symm).eq,
    ← mul_assoc, h.add]
  have he : -(-(a * -((t⁻¹ : Fˣ) : F)) * (t : F)) + a = 0 := by
    simp
  rw [he, h.zero, one_mul]
  simp only [mul_neg, neg_neg]

theorem weylWord_conj_other_outgoing (i j k : Fin n) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (t : Fˣ) (a : F) :
    MulAut.conj (weylWord x i j hij t) (x (root j k hjk) a) =
      x (root i k hik) ((t : F) * a) := by
  have he := weylWord_conj_outgoing h i j k hij hik hjk (-t) ((t : F) * a)
  have hc : -(((-t)⁻¹ : Fˣ) : F) * ((t : F) * a) = a := by
    simp
  rw [hc, ← weylWord_inv h] at he
  rw [← he]
  simp only [MulAut.conj_apply, inv_inv, ← mul_assoc, mul_inv_cancel,
    one_mul, mul_inv_cancel_right]

theorem weylWord_conj_other_incoming (i j k : Fin n) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (t : Fˣ) (a : F) :
    MulAut.conj (weylWord x i j hij t) (x (root k i hki) a) =
      x (root k j hkj) (-(a * (t : F))) := by
  have he := weylWord_conj_incoming h i j k hij hki hkj (-t) (-(a * (t : F)))
  have hc : -(a * (t : F)) * (((-t)⁻¹ : Fˣ) : F) = a := by
    simp
  rw [hc, ← weylWord_inv h] at he
  rw [← he]
  simp only [MulAut.conj_apply, inv_inv, ← mul_assoc, mul_inv_cancel,
    one_mul, mul_inv_cancel_right]

theorem weylWord_conj_root (hn : 2 < n) (i j : Fin n) (hij : i ≠ j)
    (t : Fˣ) (a : F) :
    MulAut.conj (weylWord x i j hij t) (x (root i j hij) a) =
      x (root j i hij.symm) (-((t⁻¹ : Fˣ) : F) * a * ((t⁻¹ : Fˣ) : F)) := by
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hn
  have hc := h.chain i k j hki.symm hkj hij a 1
  rw [mul_one] at hc
  rw [← hc, map_commutatorElement,
    weylWord_conj_outgoing h i j k hij hki.symm hkj.symm,
    weylWord_conj_incoming h i j k hij hki hkj,
    h.chain j k i hkj.symm hki hij.symm, one_mul]

theorem weylWord_conj_opposite_root (hn : 2 < n) (i j : Fin n) (hij : i ≠ j)
    (t : Fˣ) (a : F) :
    MulAut.conj (weylWord x i j hij t) (x (root j i hij.symm) a) =
      x (root i j hij) (-(t : F) * a * (t : F)) := by
  have he := weylWord_conj_root h hn i j hij (-t) (-(t : F) * a * (t : F))
  have hc : -(((-t)⁻¹ : Fˣ) : F) * (-(t : F) * a * (t : F)) *
      (((-t)⁻¹ : Fˣ) : F) = a := by
    simp [mul_assoc]
  rw [hc, ← weylWord_inv h] at he
  rw [← he]
  simp only [MulAut.conj_apply, inv_inv, ← mul_assoc, mul_inv_cancel,
    one_mul, mul_inv_cancel_right]

theorem torusWord_conj_outgoing (i j k : Fin n) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (t : Fˣ) (a : F) :
    MulAut.conj (torusWord x i j hij t) (x (root i k hik) a) =
      x (root i k hik) ((t : F) * a) := by
  rw [torusWord, conj_mul_apply,
    weylWord_conj_outgoing h i j k hij hik hjk,
    weylWord_conj_other_outgoing h i j k hij hik hjk]
  simp

theorem torusWord_conj_other_outgoing (i j k : Fin n) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (t : Fˣ) (a : F) :
    MulAut.conj (torusWord x i j hij t) (x (root j k hjk) a) =
      x (root j k hjk) (((t⁻¹ : Fˣ) : F) * a) := by
  rw [torusWord, conj_mul_apply,
    weylWord_conj_other_outgoing h i j k hij hik hjk,
    weylWord_conj_outgoing h i j k hij hik hjk]
  simp

theorem torusWord_conj_incoming (i j k : Fin n) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (t : Fˣ) (a : F) :
    MulAut.conj (torusWord x i j hij t) (x (root k j hkj) a) =
      x (root k j hkj) (a * (t : F)) := by
  rw [torusWord, conj_mul_apply,
    weylWord_conj_incoming h i j k hij hki hkj,
    weylWord_conj_other_incoming h i j k hij hki hkj]
  simp

theorem torusWord_conj_other_incoming (i j k : Fin n) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (t : Fˣ) (a : F) :
    MulAut.conj (torusWord x i j hij t) (x (root k i hki) a) =
      x (root k i hki) (a * ((t⁻¹ : Fˣ) : F)) := by
  rw [torusWord, conj_mul_apply,
    weylWord_conj_other_incoming h i j k hij hki hkj,
    weylWord_conj_incoming h i j k hij hki hkj]
  simp

theorem torusWord_conj_root (hn : 2 < n) (i j : Fin n) (hij : i ≠ j)
    (t : Fˣ) (a : F) :
    MulAut.conj (torusWord x i j hij t) (x (root i j hij) a) =
      x (root i j hij) ((t : F) * a * (t : F)) := by
  rw [torusWord, conj_mul_apply, weylWord_conj_root h hn,
    weylWord_conj_opposite_root h hn]
  simp

theorem torusWord_conj_opposite_root (hn : 2 < n) (i j : Fin n) (hij : i ≠ j)
    (t : Fˣ) (a : F) :
    MulAut.conj (torusWord x i j hij t) (x (root j i hij.symm) a) =
      x (root j i hij.symm) (((t⁻¹ : Fˣ) : F) * a * ((t⁻¹ : Fˣ) : F)) := by
  rw [torusWord, conj_mul_apply, weylWord_conj_opposite_root h hn,
    weylWord_conj_root h hn]
  simp

end SteinbergWords
end Theory.SpecificGroups.LinearHigher
