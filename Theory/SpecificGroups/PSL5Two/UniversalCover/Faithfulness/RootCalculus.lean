module

public import Theory.SpecificGroups.PSL5Two.UniversalCover.Presentation

/-!
# Root and coordinate-swap calculus for the binary Steinberg presentation

The three defining relations imply that each root element is an involution,
and that `xᵢⱼ xⱼᵢ xᵢⱼ` conjugates roots by the coordinate transposition `(i j)`.
In particular the opposite-root braid relation is proved, rather than added
to the presentation. Its proof expresses a root as a commutator through a
third coordinate and conjugates both factors using the chain relations.

This is the local calculation used in the type A₄ Bruhat presentation argument
for the PSL₅(2) calculation underlying Aschbacher–Smith I.1.3, printed p.407,
and GLS98 §6.1. All statements hold for any realization of the published
`Relations`, and hence for the actual `SteinbergGroup` generators.
-/

@[expose] public section

open scoped commutatorElement
namespace Theory.SpecificGroups.PSL5Two.UniversalCover

namespace Relations
variable {E : Type*} [Group E] {x : Root → E} (h : Relations x)
include h

theorem inv (r : Root) : (x r)⁻¹ = x r :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h.square r)

theorem mul_self (r : Root) : x r * x r = 1 := by
  simpa only [pow_two] using h.square r

theorem mul_self_assoc (r : Root) (a : E) : x r * (x r * a) = a := by
  rw [← mul_assoc, h.mul_self, one_mul]

theorem commute (r s : Root) (hrs : r.val.2 ≠ s.val.1) (hsr : s.val.2 ≠ r.val.1) :
    Commute (x r) (x s) :=
  commutatorElement_eq_one_iff_commute.mp (h.distant r s hrs hsr)

theorem conj_distant (r s : Root) (hrs : r.val.2 ≠ s.val.1)
    (hsr : s.val.2 ≠ r.val.1) : MulAut.conj (x r) (x s) = x s := by
  rw [conj_eq_commutatorElement_mul, h.distant r s hrs hsr, one_mul]

theorem conj_chain (i j k : Fin 5) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    MulAut.conj (x (root i j hij)) (x (root j k hjk)) =
      x (root i k hik) * x (root j k hjk) := by
  rw [conj_eq_commutatorElement_mul, h.chain i j k hij hjk hik]

theorem conj_chain_reverse (i j k : Fin 5) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) :
    MulAut.conj (x (root j k hjk)) (x (root i j hij)) =
      x (root i k hik) * x (root i j hij) := by
  rw [conj_eq_commutatorElement_mul, ← commutatorElement_inv,
    h.chain i j k hij hjk hik, h.inv]
end Relations

namespace Faithfulness
variable {E : Type*} [Group E]

def weylWord (x : Root → E) (i j : Fin 5) (hij : i ≠ j) : E :=
  x (root i j hij) * x (root j i hij.symm) * x (root i j hij)

private theorem conj_mul_apply (a b c : E) :
    MulAut.conj (a * b) c = MulAut.conj a (MulAut.conj b c) := by
  simp only [MulAut.conj_apply, mul_inv_rev, mul_assoc]

variable {x : Root → E} (h : Relations x)
include h

theorem weylWord_inv (i j : Fin 5) (hij : i ≠ j) :
    (weylWord x i j hij)⁻¹ = weylWord x i j hij := by
  simp only [weylWord, mul_inv_rev, h.inv, mul_assoc]

theorem weylWord_sq (i j : Fin 5) (hij : i ≠ j) :
    weylWord x i j hij ^ 2 = 1 := by
  rw [pow_two]
  nth_rw 1 [← weylWord_inv h i j hij]
  exact inv_mul_cancel _

theorem weylWord_conj_outgoing (i j k : Fin 5) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) :
    MulAut.conj (weylWord x i j hij) (x (root i k hik)) = x (root j k hjk) := by
  rw [weylWord, conj_mul_apply, conj_mul_apply,
    h.conj_distant (root i j hij) (root i k hik) hij.symm hik.symm,
    h.conj_chain j i k hij.symm hik hjk, map_mul,
    h.conj_chain i j k hij hjk hik,
    h.conj_distant (root i j hij) (root i k hik) hij.symm hik.symm]
  rw [(h.commute (root i k hik) (root j k hjk) hjk.symm hik.symm).eq]
  rw [mul_assoc, h.mul_self, mul_one]

theorem weylWord_conj_incoming (i j k : Fin 5) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) :
    MulAut.conj (weylWord x i j hij) (x (root k j hkj)) = x (root k i hki) := by
  rw [weylWord, conj_mul_apply, conj_mul_apply,
    h.conj_distant (root i j hij) (root k j hkj) (Ne.symm hkj) hij.symm,
    h.conj_chain_reverse k j i hkj hij.symm hki, map_mul,
    h.conj_chain_reverse k i j hki hij hkj,
    h.conj_distant (root i j hij) (root k j hkj) (Ne.symm hkj) hij.symm]
  rw [(h.commute (root k j hkj) (root k i hki) (Ne.symm hkj) (Ne.symm hki)).eq]
  rw [mul_assoc, h.mul_self, mul_one]

theorem weylWord_conj_root (i j : Fin 5) (hij : i ≠ j) :
    MulAut.conj (weylWord x i j hij) (x (root i j hij)) = x (root j i hij.symm) := by
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide : 2 < 5)
  rw [← h.chain i k j (Ne.symm hki) hkj hij, map_commutatorElement,
    weylWord_conj_outgoing h i j k hij (Ne.symm hki) (Ne.symm hkj),
    weylWord_conj_incoming h i j k hij hki hkj,
    h.chain j k i (Ne.symm hkj) hki hij.symm]

theorem weylWord_symm (i j : Fin 5) (hij : i ≠ j) :
    weylWord x i j hij = weylWord x j i hij.symm := by
  have he := weylWord_conj_root h i j hij
  rw [MulAut.conj_apply, weylWord_inv h] at he
  have hh := congrArg (fun z => x (root i j hij) * z * x (root i j hij)) he
  simpa only [weylWord, mul_assoc, h.mul_self_assoc, h.mul_self, mul_one, one_mul]
    using hh.symm


/-- The action of a coordinate permutation on the twenty roots. -/
def permuteRoot (σ : Equiv.Perm (Fin 5)) (r : Root) : Root :=
  root (σ r.val.1) (σ r.val.2) (σ.injective.ne r.property)

theorem weylWord_conj_generator (i j : Fin 5) (hij : i ≠ j) (r : Root) :
    MulAut.conj (weylWord x i j hij) (x r) =
      x (permuteRoot (Equiv.swap i j) r) := by
  obtain ⟨⟨k, l⟩, hkl⟩ := r
  change MulAut.conj (weylWord x i j hij) (x (root k l hkl)) = _
  by_cases hki : k = i
  · subst k
    by_cases hlj : l = j
    · subst l
      simpa only [permuteRoot, root, Equiv.swap_apply_left, Equiv.swap_apply_right]
        using weylWord_conj_root h i j hij
    · simpa only [permuteRoot, root, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hkl.symm hlj]
        using weylWord_conj_outgoing h i j l hij hkl (Ne.symm hlj)
  by_cases hkj : k = j
  · subst k
    rw [weylWord_symm h i j hij]
    by_cases hli : l = i
    · subst l
      simpa only [permuteRoot, root, Equiv.swap_apply_left, Equiv.swap_apply_right]
        using weylWord_conj_root h j i hij.symm
    · simpa only [permuteRoot, root, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne hli hkl.symm]
        using weylWord_conj_outgoing h j i l hij.symm hkl (Ne.symm hli)
  by_cases hli : l = i
  · subst l
    rw [weylWord_symm h i j hij]
    simpa only [permuteRoot, root, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hki hkj]
      using weylWord_conj_incoming h j i k hij.symm hkj hki
  by_cases hlj : l = j
  · subst l
    simpa only [permuteRoot, root, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hki hkj]
      using weylWord_conj_incoming h i j k hij hki hkj
  simp only [permuteRoot, root, Equiv.swap_apply_of_ne_of_ne hki hkj,
    Equiv.swap_apply_of_ne_of_ne hli hlj]
  change MulAut.conj (weylWord x i j hij) (x (root k l hkl)) = x (root k l hkl)
  rw [weylWord, conj_mul_apply, conj_mul_apply,
    h.conj_distant (root i j hij) (root k l hkl) (Ne.symm hkj) hli,
    h.conj_distant (root j i hij.symm) (root k l hkl) (Ne.symm hki) hlj,
    h.conj_distant (root i j hij) (root k l hkl) (Ne.symm hkj) hli]

theorem weylWord_conj_weylWord (i j k l : Fin 5) (hij : i ≠ j) (hkl : k ≠ l) :
    MulAut.conj (weylWord x i j hij) (weylWord x k l hkl) =
      weylWord x (Equiv.swap i j k) (Equiv.swap i j l)
        ((Equiv.swap i j).injective.ne hkl) := by
  conv_lhs => arg 2; unfold weylWord
  simp only [map_mul, weylWord_conj_generator h]
  rfl

end Faithfulness
end Theory.SpecificGroups.PSL5Two.UniversalCover
