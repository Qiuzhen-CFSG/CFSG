module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Support
import Mathlib.Tactic.FinCases

/-!
# Bounded finite checks and transport for the Held factor certificates

Finite checks are split into small blocks to bound kernel memory. Faithful
maps and conjugate generating sets preserve the order of the literal closure.
These elementary tools do not assume any order or recognition fact about Held.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors
open Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate

def blockIndex (n m : ℕ) (hn : 0 < n) (k j : ℕ) : Fin n :=
  ⟨(k * m + j) % n, Nat.mod_lt _ hn⟩

theorem allBlocks {n m b : ℕ} (hn : 0 < n) (hm : 0 < m) (hnb : n ≤ b * m)
    (P : Fin n → Prop)
    (h : ∀ k : Fin b, ∀ j : Fin m, P (blockIndex n m hn k.val j.val)) : ∀ x, P x := by
  intro x
  have hk : x.val / m < b := (Nat.div_lt_iff_lt_mul hm).mpr (x.isLt.trans_le hnb)
  have h' := h ⟨x.val / m, hk⟩ ⟨x.val % m, Nat.mod_lt _ hm⟩
  have he : blockIndex n m hn (x.val / m) (x.val % m) = x := by
    apply Fin.ext
    simp only [blockIndex, Nat.div_add_mod', Nat.mod_eq_of_lt x.isLt]
  rwa [he] at h'

variable {G H I J : Type*} [Group G] [Group H]

theorem card_closure_image (f : G →* H) (hf : Function.Injective f) (g : I → G) :
    Nat.card (Subgroup.closure (Set.range g)) =
      Nat.card (Subgroup.closure (Set.range (fun i => f (g i)))) := by
  rw [← Subgroup.card_map_of_injective hf, MonoidHom.map_closure, ← Set.range_comp]
  rfl

theorem card_closure_equiv (e : G ≃* H) (g : I → G) (h : J → H)
    (hg : ∀ i, e (g i) ∈ Subgroup.closure (Set.range h))
    (hh : ∀ j, e.symm (h j) ∈ Subgroup.closure (Set.range g)) :
    Nat.card (Subgroup.closure (Set.range g)) = Nat.card (Subgroup.closure (Set.range h)) := by
  have he : (Subgroup.closure (Set.range g)).map e.toMonoidHom =
      Subgroup.closure (Set.range h) := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨i, rfl⟩
      exact hg i
    · apply (Subgroup.closure_le _).mpr
      rintro _ ⟨j, rfl⟩
      exact ⟨e.symm (h j), hh j, e.apply_symm_apply _⟩
  rw [← he, Subgroup.card_map_of_injective e.injective]

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors
