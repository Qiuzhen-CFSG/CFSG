/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Combinatorics/HexadIntersectionCounts.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

/-!
# HexadIntersectionCounts

The 77 hexads on 22 points have controlled disjointness and common-disjointness counts.
Double counting point and pair incidences supplies the graph parameters.

Source: Gerald Höhn, ATLAS, `Atlas/Combinatorics/HexadIntersectionCounts.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section
namespace Atlas.Combinatorics
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

/-- The incidence data used for the 77-hexad graph. -/
structure HexadDesignData (blocks : Finset (Finset V)) : Prop where
  card : blocks.card = 77
  size : ∀ B ∈ blocks, B.card = 6
  point : ∀ b, (blocks.filter (fun B => b ∈ B)).card = 21
  pair : ∀ b c, b ≠ c → (blocks.filter (fun B => b ∈ B ∧ c ∈ B)).card = 5
  intersection : ∀ B ∈ blocks, ∀ C ∈ blocks, B ≠ C →
    (B ∩ C).card = 0 ∨ (B ∩ C).card = 2

theorem hexad_intersection_sum (blocks : Finset (Finset V)) (h : HexadDesignData blocks)
    (B : Finset V) (hB : B ∈ blocks) : (∑ E ∈ blocks,(B ∩ E).card) = 126 := by
  rw [Finset.sum_card_inter (fun b _ => h.point b),h.size B hB]

theorem hexad_disjoint_card (blocks : Finset (Finset V)) (h : HexadDesignData blocks)
    (B : Finset V) (hB : B ∈ blocks) :
    (blocks.filter (fun E => (B ∩ E).card = 0)).card = 16 := by
  let S := blocks.erase B
  have hi (E : Finset V) (hE : E ∈ S) : (B ∩ E).card = 0 ∨ (B ∩ E).card = 2 :=
    h.intersection B hB E (Finset.mem_erase.mp hE).2 (Ne.symm (Finset.mem_erase.mp hE).1)
  have hc : S.card = 76 := by rw [Finset.card_erase_of_mem hB,h.card]
  have hs := hexad_intersection_sum blocks h B hB
  have he := Finset.sum_erase_add (s := blocks) (f := fun E => (B ∩ E).card) hB
  rw [Finset.inter_self,h.size B hB,hs] at he
  have hf : (∑ E ∈ S,(B ∩ E).card) =
      2*(S.filter (fun E => (B ∩ E).card ≠ 0)).card := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun E => (B ∩ E).card = 0)]
    have hz : (∑ E ∈ S.filter (fun E => (B ∩ E).card = 0),(B ∩ E).card) = 0 :=
      Finset.sum_eq_zero (fun E hE => (Finset.mem_filter.mp hE).2)
    rw [hz,zero_add]
    rw [Finset.sum_congr rfl (fun E hE => (hi E (Finset.mem_filter.mp hE).1).resolve_left
      (Finset.mem_filter.mp hE).2)]
    simp [Nat.mul_comm]
  change (∑ E ∈ S,(B ∩ E).card)+6=126 at he
  rw [hf] at he
  have hp := Finset.card_filter_add_card_filter_not (s := S) (p := fun E => (B ∩ E).card = 0)
  rw [hc] at hp
  have hn0 : (S.filter (fun E => (B ∩ E).card ≠ 0)).card = 60 := by omega
  have hn1 : (S.filter (fun E => ¬(B ∩ E).card = 0)).card = 60 := by
    exact hn0
  rw [hn1] at hp
  have hn : (S.filter (fun E => (B ∩ E).card = 0)).card = 16 := by omega
  have heq : blocks.filter (fun E => (B ∩ E).card = 0) = S.filter (fun E => (B ∩ E).card = 0) := by
    ext E
    by_cases he : E = B
    · subst E
      simp only [S,Finset.mem_filter,Finset.mem_erase,Finset.inter_self,h.size B hB]
      norm_num
    · simp [S,he]
  rw [heq,hn]

theorem hexad_pair_incidence_sum (blocks : Finset (Finset V)) (h : HexadDesignData blocks)
    (B C : Finset V) (hB : B ∈ blocks) (hC : C ∈ blocks) :
    (∑ E ∈ blocks,(B ∩ E).card*(C ∩ E).card) = 180+16*(B ∩ C).card := by
  have hinter (D E : Finset V) : (D ∩ E).card = ∑ d ∈ D,if d ∈ E then 1 else 0 := by
    rw [← Finset.card_filter,Finset.filter_mem_eq_inter]
  have he (E : Finset V) : (B ∩ E).card*(C ∩ E).card =
      ∑ b ∈ B,∑ c ∈ C,if b ∈ E ∧ c ∈ E then 1 else 0 := by
    rw [hinter B E,hinter C E,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    by_cases hbE : b ∈ E <;> by_cases hcE : c ∈ E <;> simp [hbE,hcE]
  simp_rw [he]
  rw [Finset.sum_comm]
  have hf (b : V) : (∑ E ∈ blocks,∑ c ∈ C,if b ∈ E ∧ c ∈ E then 1 else 0) =
      ∑ c ∈ C,if b = c then 21 else 5 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c hc
    rw [← Finset.card_filter]
    by_cases hbc : b = c
    · subst c; simpa using h.point b
    · rw [h.pair b c hbc,if_neg hbc]
  simp_rw [hf]
  have hg (b c : V) : (if b = c then 21 else 5) = 5+(if b = c then 16 else 0) := by
    split_ifs <;> rfl
  simp_rw [hg,Finset.sum_add_distrib]
  simp only [Finset.sum_const,nsmul_eq_mul,h.size C hC]
  have hsum (b : V) : (∑ c ∈ C,if b = c then 16 else 0) = if b ∈ C then 16 else 0 := by simp
  simp_rw [hsum]
  simp only [h.size B hB]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.sum_const,nsmul_eq_mul]
  ring_nf
  congr 2

theorem hexad_common_disjoint_card (blocks : Finset (Finset V)) (h : HexadDesignData blocks)
    (B C : Finset V) (hB : B ∈ blocks) (hC : C ∈ blocks) (hBC : B ≠ C) :
    (blocks.filter (fun E => (B ∩ E).card = 0 ∧ (C ∩ E).card = 0)).card =
      2*(B ∩ C).card := by
  let s := (B ∩ C).card
  have hs : s = 0 ∨ s = 2 := h.intersection B hB C hC hBC
  have hprod (E : Finset V) (hE : E ∈ blocks) :
      (B ∩ E).card*(C ∩ E).card =
      4*(if (B ∩ E).card ≠ 0 ∧ (C ∩ E).card ≠ 0 then 1 else 0)+
      (if E = B then 4*s else 0)+(if E = C then 4*s else 0) := by
    by_cases heB : E = B
    · subst E
      have hc : (C ∩ B).card = s := by rw [Finset.inter_comm]
      rw [Finset.inter_self,h.size B hB,hc]
      rcases hs with hs | hs <;> simp [hs,hBC]
    · by_cases heC : E = C
      · subst E
        have hb : (B ∩ C).card = s := rfl
        rw [Finset.inter_self,h.size C hC,hb]
        rcases hs with hs | hs <;> simp [hs,Ne.symm hBC]
      · rcases h.intersection B hB E hE (Ne.symm heB) with hb | hb <;>
          rcases h.intersection C hC E hE (Ne.symm heC) with hc | hc <;>
          simp [hb,hc,heB,heC]
  have hp := Finset.sum_congr rfl hprod
  rw [hexad_pair_incidence_sum blocks h B C hB hC] at hp
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hp
  simp only [Finset.sum_ite_eq',hB,hC,ite_true] at hp
  rw [← Finset.card_filter] at hp
  have hpoint (E : Finset V) :
      (if (B ∩ E).card = 0 ∧ (C ∩ E).card = 0 then 1 else 0)+1 =
      (if (B ∩ E).card = 0 then 1 else 0)+(if (C ∩ E).card = 0 then 1 else 0)+
      (if (B ∩ E).card ≠ 0 ∧ (C ∩ E).card ≠ 0 then 1 else 0) := by
    by_cases hb : (B ∩ E).card = 0 <;> by_cases hc : (C ∩ E).card = 0 <;> simp [hb,hc]
  have he := Finset.sum_congr (s₁ := blocks) rfl (fun E _ => hpoint E)
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one,
    ← Finset.card_filter] at he
  rw [h.card,hexad_disjoint_card blocks h B hB,hexad_disjoint_card blocks h C hC] at he
  change 180+16*s = _ at hp
  omega
theorem hexad_point_disjoint_card (blocks : Finset (Finset V)) (h : HexadDesignData blocks)
    (B : Finset V) (hB : B ∈ blocks) (j : V) (hj : j ∉ B) :
    (blocks.filter (fun E => j ∈ E ∧ (B ∩ E).card = 0)).card = 6 := by
  let S := blocks.filter (fun E => j ∈ E)
  have hc : S.card = 21 := h.point j
  have hp (b : V) (hb : b ∈ B) : (S.filter (fun E => b ∈ E)).card = 5 := by
    rw [Finset.filter_filter]
    exact h.pair j b (fun he => hj (he ▸ hb))
  have hsum : (∑ E ∈ S,(B ∩ E).card) = 30 := by
    rw [Finset.sum_card_inter hp,h.size B hB]
  have hi (E : Finset V) (hE : E ∈ S) : (B ∩ E).card = 0 ∨ (B ∩ E).card = 2 :=
    h.intersection B hB E (Finset.mem_filter.mp hE).1
      (fun he => hj (he.symm ▸ (Finset.mem_filter.mp hE).2))
  have he : (∑ E ∈ S,(B ∩ E).card) = 2*(S.filter (fun E => (B ∩ E).card ≠ 0)).card := by
    have hf (E : Finset V) (hE : E ∈ S) :
        (B ∩ E).card = 2*(if (B ∩ E).card ≠ 0 then 1 else 0) := by
      rcases hi E hE with hE | hE <;> simp [hE]
    rw [Finset.sum_congr rfl hf,← Finset.mul_sum,← Finset.card_filter]
  rw [he] at hsum
  have hn0 : (S.filter (fun E => (B ∩ E).card ≠ 0)).card = 15 := by omega
  have hn1 : (S.filter (fun E => ¬(B ∩ E).card = 0)).card = 15 := by
    exact hn0
  have hh := Finset.card_filter_add_card_filter_not (s := S) (p := fun E => (B ∩ E).card = 0)
  rw [hn1,hc] at hh
  have hz : (S.filter (fun E => (B ∩ E).card = 0)).card = 6 := by omega
  simpa only [S,Finset.filter_filter] using hz
end Atlas.Combinatorics
