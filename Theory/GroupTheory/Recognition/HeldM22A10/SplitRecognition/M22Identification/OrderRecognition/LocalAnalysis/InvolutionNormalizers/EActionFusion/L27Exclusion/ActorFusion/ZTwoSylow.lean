module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.Nonfusion

/-!
# The Sylow subgroup of the second vector centralizer

The elementary sixteen E centralizes printed z₂. Its normalizer inside
C_G(z₂) has order 336 = 16 · 21 by the two normalizer orbits. The Sylow
normalizer congruence then rules out 32 dividing |C_G(z₂)|: it would also
divide 336. Hence E, restricted to the actual centralizer, is Sylow there.

This supplies the elementary abelian Sylow input to the source analysis
of C_G(z₂), without a recognition theorem or actor fusion.
Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 6, printed p.6. Printed z₂ is `z 1`.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

omit [Finite G] in
/-- The actual elementary sixteen centralizes printed z₂. -/
public theorem l27_E_le_z_one_centralizer :
    E D k ≤ centralizer ({into D k (z 1)} : Set G) := by
  let := E_elementary D k
  have hzE : into D k (z 1) ∈ E D k :=
    modelE_map D k ▸ mem_map_of_mem _ (z_mem_modelE 1)
  intro x hx
  exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm hx hzE)

/-- The normalizer inside C_G(z₂) has odd index over E. -/
public theorem l27_z_one_sylow_normalizer_card
    (h168 : Nat.card (eNormalizerQuotient D k) = 168) :
    Nat.card (normalizer
      (((E D k).subgroupOf (centralizer ({into D k (z 1)} : Set G))) :
        Set (centralizer ({into D k (z 1)} : Set G)))) = 336 := by
  rw [← subgroupOf_normalizer_eq (l27_E_le_z_one_centralizer D k)]
  rw [← inf_subgroupOf_right]
  rw [Nat.card_congr (subgroupOfEquivOfLe (show
    normalizer (E D k : Set G) ⊓ centralizer ({into D k (z 1)} : Set G) ≤
      centralizer ({into D k (z 1)} : Set G) from inf_le_right)).toEquiv]
  rw [inf_comm]
  exact z_one_centralizer_inf_normalizer_card_of_168 D k h168

/-- The actual E is a Sylow two-subgroup of C_G(z₂). -/
public theorem l27_E_sylow_in_z_one_centralizer
    (h168 : Nat.card (eNormalizerQuotient D k) = 168) :
    ∃ S : Sylow 2 (centralizer ({into D k (z 1)} : Set G)),
      (S : Subgroup _) = (E D k).subgroupOf
        (centralizer ({into D k (z 1)} : Set G)) := by
  let H := centralizer ({into D k (z 1)} : Set G)
  let B := (E D k).subgroupOf H
  have hB : Nat.card B = 2 ^ 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (l27_E_le_z_one_centralizer D k)).toEquiv]
    exact E_card D k
  have hindex : ¬ 2 ∣ B.index := by
    intro hdiv
    have hc : 2 ^ (4 + 1) ∣ Nat.card H := by
      rw [← B.card_mul_index, hB, pow_succ]
      exact Nat.mul_dvd_mul_left _ hdiv
    have hn := Sylow.prime_pow_dvd_card_normalizer hc hB
    rw [l27_z_one_sylow_normalizer_card D k h168] at hn
    norm_num at hn
  exact ⟨(IsPGroup.of_card hB).toSylow hindex, rfl⟩

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
