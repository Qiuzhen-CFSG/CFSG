module

public import Theory.GroupAction.Lemmas
public import Theory.GroupAction.Quotient

/-!
# Strict cardinal inequalities for finite groups

Proper subgroups and quotients by nontrivial normal subgroups have smaller
order. The proofs compare subgroup indices and quotient cardinalities.
Extracted from `FeitThompson/GroupAction/Cardinalities.lean` for strong
induction on finite groups; public names and statements are unchanged.
-/

open Subgroup

section StrictInequalities

variable {G : Type*} [Group G] [Finite G]

/-- If `H` is a non-trivial normal subgroup, then `|G/H| < |G|`. -/
public lemma natCard_quotient_lt_natCard_of_ne_bot (H : Subgroup G) [H.Normal] (hH : H ≠ ⊥) :
    Nat.card (G ⧸ H) < Nat.card G := by
  have hH_one_lt : 1 < Nat.card H := (Subgroup.one_lt_card_iff_ne_bot (H := H)).2 hH
  have hcard_mul : Nat.card G = Nat.card (G ⧸ H) * Nat.card H := by
    simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := G) (s := H))
  have hlt : Nat.card (G ⧸ H) * 1 < Nat.card (G ⧸ H) * Nat.card H :=
    Nat.mul_lt_mul_of_pos_left hH_one_lt (Nat.card_pos (α := G ⧸ H))
  simpa [hcard_mul] using hlt

/-- If `H < K` are subgroups of a finite group, then `|H| < |K|`. -/
public lemma natCard_lt_of_subgroup_lt {H K : Subgroup G} (hHK : H < K) :
    Nat.card H < Nat.card K := by
  let HK : Subgroup K := H.subgroupOf K
  have hHK_card : Nat.card HK = Nat.card H := natCard_subgroupOf_eq H K hHK.1
  have hHK_ne_top : HK ≠ ⊤ := by
    intro htop
    apply hHK.2
    intro x hx
    have hx_top : (⟨x, hx⟩ : K) ∈ (⊤ : Subgroup K) := by simp
    have hx_HK : (⟨x, hx⟩ : K) ∈ HK := by simp [htop]
    simpa [HK, Subgroup.mem_subgroupOf] using hx_HK
  have hle : Nat.card HK ≤ Nat.card K := Subgroup.card_le_card_group (H := HK)
  have hne : Nat.card HK ≠ Nat.card K := by
    intro hEq
    exact hHK_ne_top ((Subgroup.card_eq_iff_eq_top (H := HK)).1 hEq)
  have hlt : Nat.card HK < Nat.card K := lt_of_le_of_ne hle hne
  simpa [hHK_card] using hlt

end StrictInequalities
