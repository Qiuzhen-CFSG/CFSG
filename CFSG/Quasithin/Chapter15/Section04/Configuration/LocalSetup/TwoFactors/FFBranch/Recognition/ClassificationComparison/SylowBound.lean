module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.Prepared
/-!
# The Sylow bound common to all retained F.6.18 rows

Each row explicitly identifies the common local subgroup or supplies its
extension maps. Their orders are at most 128. In the two solvable ambient
models even the entire group has order at most 108. Thus every Sylow
two-subgroup of a classified action has order at most 128. The argument uses
all twelve remaining rows, in either ordering of the generators, and keeps
field and module alternatives unchanged.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, F.6.18, printed pp.309–310.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace GoldschmidtAlternatives
variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

omit [Finite D] in
/-- Cardinality of an actual extension in the source rows. -/
theorem Extension.card {A B : Type*} [Group A] [Group B] (h : Extension D A B) :
    Nat.card D = Nat.card A * Nat.card B := by
  obtain ⟨f, hf, ⟨e⟩⟩ := h
  let q := QuotientGroup.quotientKerEquivOfSurjective f hf
  calc
    Nat.card D = Nat.card f.ker * Nat.card (D ⧸ f.ker) := by
      rw [← Subgroup.index_eq_card, Subgroup.card_mul_index]
    _ = Nat.card A * Nat.card B := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr q.toEquiv]

private theorem ordered_intersection_card_le (h : RemainingOrdered G₁ G₂) :
    Nat.card (G₁ ⊓ G₂ : Subgroup D) ≤ 128 := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · apply (Nat.card_le_card_of_injective (G₁ ⊓ G₂ : Subgroup D).subtype
      Subtype.val_injective).trans
    rcases h with h | h
    · obtain ⟨e⟩ := h
      rw [Nat.card_congr e.toEquiv]
      norm_num [S3, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    · rw [h.card, HeisenbergPrime.card]
      norm_num [ E4, C, Nat.card_prod, Nat.card_eq_fintype_card]
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨e⟩, _⟩ := h
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    norm_num
  · obtain ⟨_, _, _, _, ⟨e⟩, _⟩ := h
    rw [Nat.card_congr e.toEquiv]
    norm_num [E4, C, Nat.card_prod, Nat.card_eq_fintype_card]
  · obtain ⟨_, _, _, _, ⟨e⟩, _⟩ := h
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    norm_num
  · obtain ⟨_, ⟨e⟩, _⟩ := h
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    norm_num
  · obtain ⟨_, ⟨e⟩, _⟩ := h
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    norm_num
  · obtain ⟨_, ⟨e⟩, _⟩ := h
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
    norm_num [C, Nat.card_eq_fintype_card]
  · obtain ⟨_, ⟨e⟩, _⟩ := h
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
    norm_num [C, Nat.card_eq_fintype_card]
  · obtain ⟨_, _, _, ⟨e⟩, _⟩ := h
    rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card]
    norm_num [C, Nat.card_eq_fintype_card]
  · obtain ⟨_, _, _, ht, _⟩ := h
    rw [ht.card]
    norm_num [C4Square, E4, C, Nat.card_prod, Nat.card_eq_fintype_card]
  · rw [h.2.1.card]
    norm_num [C4Square, E4, C, Nat.card_prod, Nat.card_eq_fintype_card]
  · rw [h.2.1.card, DihedralGroup.nat_card]
    norm_num [C4Square, C, Nat.card_prod, Nat.card_eq_fintype_card]

/-- All twelve retained F.6.18 rows bound the actual common subgroup by 128. -/
theorem Remaining.intersection_card_le (h : Remaining G₁ G₂) :
    Nat.card (G₁ ⊓ G₂ : Subgroup D) ≤ 128 := by
  rcases h with h | h
  · exact ordered_intersection_card_le h
  · simpa only [inf_comm] using ordered_intersection_card_le h
end GoldschmidtAlternatives

universe u v
/-- The uniform bound is on every actual ambient Sylow subgroup. -/
theorem ClassifiedAction.sylow_card_le {D : Type u} [Group D] [Finite D]
    {K : GroupClass.{u}} {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}
    (h : ClassifiedAction K ρ G₁ G₂) (S : Sylow 2 D) : Nat.card S ≤ 128 := by
  obtain ⟨T, hT⟩ := h.triple.intersection_sylow
  rw [Nat.card_congr (S.equiv T).toEquiv,
    ← Nat.card_congr (MulEquiv.subgroupCongr hT).toEquiv]
  exact h.goldschmidt.intersection_card_le
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
