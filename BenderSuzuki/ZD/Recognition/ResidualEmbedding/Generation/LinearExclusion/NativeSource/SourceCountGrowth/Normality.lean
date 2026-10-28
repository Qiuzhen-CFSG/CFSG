module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.SourceCountGrowth.Counting

/-!
# Normality of the first source normalizer

If R₁<V, the second proper normalizer section N_V(R₁)/R₁ has at least q
cosets by the same coprime torus calculation. Its order is therefore at
least q³|U|, the established upper bound for V. Equality gives N_V(R₁)=V
and M=VD. The actual D normalizes AU and hence R₁, proving R₁ normal in M.
If R₁=V, normality is immediate. The supplement is only used in the branch
where its cardinal proof establishes it.

Source: GLS IV, Chapter 2, Lemma 15.6, second paragraph.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion.SourceCount
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
local notation "D" => residualPairStabilizer M t
local notation "K" => residualCommutator M t
local notation "V" => pointCore M
local notation "U" => twoCore M z t
local notation "A" => closure (Z ∩ (M : Set G))
local notation "R" => sourceNormalizer Z M z t

public theorem sourceNormalizer_relative_normal (hs : CentralizerLocalTwoData d) :
    ((R).subgroupOf M).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  by_cases hRV : R = V
  · rw [hRV]
    exact point_normalizes_pointCore
  have hlt : R < V := lt_of_le_of_ne inf_le_left hRV
  let W := V ⊓ normalizer (R : Set G)
  have hRW : R < W := pgroup_lt_relative_normalizer
    ((pCore_isPGroup (p := 2) (G := M)).map M.subtype) hlt
  have hKV : K ≤ normalizer (V : Set G) := by
    rw [d.torus_structure.1]
    exact (inf_le_left.trans inf_le_left).trans point_normalizes_pointCore
  have hKW : K ≤ normalizer (W : Set G) :=
    (le_inf hKV ((torus_normalizes_sourceNormalizer d hs).trans le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hindex := torus_section_index_lower d hs W R inf_le_left hRW inf_le_right
    (le_sup_right.trans (sup_le_sourceNormalizer d hs)) hKW
    (torus_normalizes_sourceNormalizer d hs)
  have hWcard : (2 ^ n) ^ 3 * Nat.card U ≤ Nat.card W := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup G) R W bot_le hRW.le
    simp only [relIndex_bot_left] at hc
    rw [sourceNormalizer_card d hs] at hc
    calc
      _ = ((2 ^ n) ^ 2 * Nat.card U) * 2 ^ n := by ring
      _ ≤ ((2 ^ n) ^ 2 * Nat.card U) * (R).relIndex W := Nat.mul_le_mul_left _ hindex
      _ = _ := hc
  have hWV : W = V := eq_of_le_of_card_ge inf_le_left
    ((pointCore_card_upper d hs).trans hWcard)
  have hVcard : Nat.card V = (2 ^ n) ^ 3 * Nat.card U :=
    le_antisymm (pointCore_card_upper d hs) (hWV ▸ hWcard)
  have hM : V ⊔ D = M := by
    apply eq_of_le_of_card_ge (sup_le (map_subtype_le _) inf_le_left)
    have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes V D
      (inf_le_left.trans point_normalizes_pointCore)
    have hi : V ⊓ D = U := by rw [inf_comm]; exact hs.pair_core_eq
    rw [hi, hVcard] at hp
    have hm := linear_stabilizer_card_of_degree d.action d.t_not_mem_M d.degree_and_fixed.1
    have he : Nat.card U * Nat.card M = Nat.card U * Nat.card (V ⊔ D : Subgroup G) := by
      rw [hm, ← hp]
      ring
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos he).le
  exact hM.ge.trans (sup_le (hWV.ge.trans inf_le_right)
    (pair_normalizes_sourceNormalizer d hs))

end BenderSuzuki.ZD.LinearExclusion.SourceCount
