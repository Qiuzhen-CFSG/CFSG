module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding.ComplementAction.Transitions
import Mathlib.Tactic.FinCases

/-!
# Order and faithful action of the fixed HS complement

The checked word tree identifies 1440 distinct elements of the exact subgroup
`H`. Right multiplication by both generators and their inverses proves that
these exhaust `H`. For each nonidentity element a checked point distinguishes
its two products with one of the defining generators of `D`; thus `C_H(D) = 1`.
No recognition of `D`, ambient order, or full-centralizer bound is needed.

These are the order and faithfulness inputs to the product embedding for
Aschbacher–Smith 16.1.5(10), printed p.1172; GLS3 Table 5.3m, class 2B.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding
open Subgroup Theory.GroupTheory Sporadic.LeechRelated.HS

namespace ComplementCertificate

theorem element_zero : element 0 = 1 := rfl

theorem value_spec (i : Fin 1440) (p : Fin 100) :
    inclusion (element i) p = value i p := by
  have aux : ∀ (n : ℕ) (j : Fin 1440), j.val = n → ∀ q : Fin 100,
      inclusion (element j) q = value j q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj q
      by_cases hzero : j = 0
      · subst j
        simpa only [element_zero, map_one, Equiv.Perm.one_apply] using (value_zero q).symm
      obtain ⟨hlt, hw, hn⟩ := word_data j hzero
      have hp := ih (parent j).val (hj ▸ hlt) (parent j) rfl
      have he : element j = element (parent j) * hLetter (parentLetter j) := by
        simp only [element, hw, evalWord_append, evalWord, mul_one]
      rw [he, map_mul]
      change inclusion (element (parent j))
        (inclusion (hLetter (parentLetter j)) q) = value j q
      rw [hp, ← letterValue_spec, ← value_step, hn]
  exact aux i.val i rfl p

theorem element_step (i : Fin 1440) (s : Fin 4) :
    element i * hLetter s = element (next i s) := by
  apply Sporadic.LeechRelated.HS.inclusion_injective
  apply Equiv.ext
  intro p
  rw [map_mul]
  change inclusion (element i) (inclusion (hLetter s) p) = inclusion (element (next i s)) p
  rw [value_spec, value_spec, ← letterValue_spec, value_step]

theorem element_injective : Function.Injective element := by
  intro i j h
  have h0 : value i 0 = value j 0 := by rw [← value_spec, ← value_spec, h]
  have h1 : value i 1 = value j 1 := by rw [← value_spec, ← value_spec, h]
  have h2 : value i 2 = value j 2 := by rw [← value_spec, ← value_spec, h]
  rw [← decode_value i, h0, h1, h2, decode_value]

private theorem hLetter_mem (s : Fin 4) : hLetter s ∈ H := by
  fin_cases s
  · exact subset_closure (by simp [hLetter])
  · exact subset_closure (by simp [hLetter])
  · exact H.inv_mem (subset_closure (by simp))
  · exact H.inv_mem (subset_closure (by simp))

private theorem closure_hLetter : closure (Set.range hLetter) = H := by
  apply le_antisymm
  · exact (closure_le _).mpr (by rintro _ ⟨s, rfl⟩; exact hLetter_mem s)
  · apply (closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact subset_closure ⟨0, rfl⟩
    · rw [Set.mem_singleton_iff.mp hx]
      exact subset_closure ⟨1, rfl⟩

theorem element_mem (i : Fin 1440) : element i ∈ H := hWord_mem (words i)

theorem element_cover (x : Carrier) (hx : x ∈ H) :
    ∃ i : Fin 1440, x = element i := by
  rw [← closure_hLetter] at hx
  induction hx using Subgroup.closure_induction_right with
  | one => exact ⟨0, element_zero.symm⟩
  | mul_right x _ y hy ih =>
    obtain ⟨s, rfl⟩ := hy
    obtain ⟨i, rfl⟩ := ih
    exact ⟨next i s, element_step i s⟩
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨s, rfl⟩ := hy
    obtain ⟨i, rfl⟩ := ih
    rw [← inverseLetter_spec]
    exact ⟨next i (inverseLetter s), element_step i (inverseLetter s)⟩

private theorem dGenerator_mem (s : Fin 2) : dGenerator s ∈ D := by
  fin_cases s
  · exact subset_closure (by simp [dGenerator])
  · exact subset_closure (by simp [dGenerator])

/-- Only row zero centralizes the defining subgroup `D`. -/
theorem centralizing_index (i : Fin 1440)
    (hi : element i ∈ centralizer (D : Set Carrier)) : i = 0 := by
  by_contra hne
  have hc : dGenerator (badGenerator i) * element i =
      element i * dGenerator (badGenerator i) :=
    mem_centralizer_iff.mp hi _ (dGenerator_mem _)
  have hp := congrArg (fun x : Carrier => inclusion x (badPoint i)) hc
  have he : dValue (badGenerator i) (value i (badPoint i)) =
      value i (dValue (badGenerator i) (badPoint i)) := by
    simpa only [map_mul, Equiv.Perm.mul_apply, value_spec, ← dValue_spec] using hp
  exact noncentral_value i hne he.symm

end ComplementCertificate

/-- The specified complement candidate has exactly 1440 elements. -/
theorem H_card : Nat.card H = 1440 := by
  let f : Fin 1440 → H := fun i => ⟨ComplementCertificate.element i,
    ComplementCertificate.element_mem i⟩
  have hi : Function.Injective f := fun _ _ h =>
    ComplementCertificate.element_injective (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro x
    obtain ⟨i, hi⟩ := ComplementCertificate.element_cover x x.property
    exact ⟨i, Subtype.ext hi.symm⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi, hs⟩)).symm.trans (Nat.card_fin 1440)

/-- Conjugation of `H` on the exact subgroup `D` has trivial kernel. -/
theorem H_inf_centralizer_D : H ⊓ centralizer (D : Set Carrier) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨i, rfl⟩ := ComplementCertificate.element_cover x hx.1
  have hi := ComplementCertificate.centralizing_index i hx.2
  rw [hi]
  exact mem_bot.mpr ComplementCertificate.element_zero

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding
