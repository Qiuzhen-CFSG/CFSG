module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.Theta
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The local normalizer restriction in the larger-field case

The identity θ(M ∩ H) = Y₀ recovers Y₀ from its product with O₂(H).
Consequently normalizers lift through H → H/O₂(H). Taking theta and
intersecting with the component closure yields θ(N_{L₀*}(Y₀*)) = Y₀*.
The earlier quotient Y₀/O₂(Y₀) of order three bounds the Sylow three-order
in every image of Y₀; component generation supplies the lower rank bound.

Only local algebra is proved here. Borel containment and the normalizer
calculations for concrete Lie-type models remain separate obligations.
The Sylow and quotient-cardinality inputs are explicit; no three-rank
restriction is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49, printed p.1144, immediately after (k).
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields
variable {G : Type*} [Group G]

/-- No extra normalizers of Y₀ appear in the literal star quotient. -/
theorem star_normalizer (H M Y0 : Subgroup G)
    (hθ : theta (M ⊓ H) = Y0) (hN : normalizer (Y0 : Set G) = M)
    (hcore : localTwoCore H ≤ M) :
    normalizer (starImage H Y0 : Set (H ⧸ pCore 2 H)) = starImage H (M ⊓ H) := by
  have hYH : Y0 ≤ H := (hθ ▸ theta_le _).trans inf_le_right
  have htheta : theta ((M ⊓ H).subgroupOf H) = Y0.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [theta_map_of_injective _ H.subtype_injective,
      map_subgroupOf_eq_of_le inf_le_right, hθ, map_subgroupOf_eq_of_le hYH]
  have hnorm : normalizer (Y0.subgroupOf H : Set H) = (M ⊓ H).subgroupOf H := by
    rw [← subgroupOf_normalizer_eq hYH, hN]
    ext x
    exact ⟨fun hx => ⟨hx, x.property⟩, fun hx => hx.1⟩
  exact image_normalizer_of_theta (QuotientGroup.mk' (pCore 2 H))
    (QuotientGroup.mk'_surjective _) (Y0.subgroupOf H) ((M ⊓ H).subgroupOf H)
    (comap_mono (hθ ▸ theta_le _))
    (by
      rw [QuotientGroup.ker_mk']
      intro x hx
      exact ⟨hcore (mem_map_of_mem H.subtype hx), x.property⟩)
    htheta hnorm

/-- The theta of the normalizer inside the component closure is exactly Y₀*. -/
theorem theta_star_component_normalizer [Finite G] (H M L0 Y0 : Subgroup G)
    (hθ : theta (M ⊓ H) = Y0) (hN : normalizer (Y0 : Set G) = M)
    (hcore : localTwoCore H ≤ M) (hYL0 : Y0 ≤ L0) :
    theta (starImage H L0 ⊓ normalizer (starImage H Y0 : Set (H ⧸ pCore 2 H))) =
      starImage H Y0 := by
  have htheta : theta (starImage H (M ⊓ H)) = starImage H Y0 := by
    rw [← FactorGeneration.starImage_theta H (M ⊓ H) inf_le_right, hθ]
  have hfix : theta (starImage H Y0) = starImage H Y0 := by
    rw [← htheta, theta_idempotent]
  apply le_antisymm
  · rw [star_normalizer H M Y0 hθ hN hcore]
    exact (theta_mono inf_le_right).trans_eq htheta
  · calc
      starImage H Y0 = theta (starImage H Y0) := hfix.symm
      _ ≤ _ := theta_mono (le_inf (map_mono (comap_mono hYL0)) (starImage H Y0).le_normalizer)

/-- The earlier order-three quotient of Y₀ bounds every three-subgroup of its star image. -/
theorem star_threeRank_le_one [Finite G] (H Y0 : Subgroup G)
    (hcard : Nat.card ((Y0.subgroupOf H) ⧸ pCore 2 (Y0.subgroupOf H)) = 3) :
    primeRank 3 (starImage H Y0) ≤ 1 := by
  let Y := Y0.subgroupOf H
  let P : Sylow 3 Y := default
  have hd : Nat.card P ∣ Nat.card Y := card_dvd_of_injective (P : Subgroup Y).subtype (P : Subgroup Y).subtype_injective
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := Y)).exists_card_eq
  have hsize : Nat.card Y = 2 ^ k * 3 := by
    rw [← (pCore 2 Y).card_mul_index, hk, index_eq_card, hcard]
  rw [hsize] at hd
  obtain ⟨j, hj⟩ := P.isPGroup'.exists_card_eq
  have hcop : Nat.Coprime (Nat.card P) (2 ^ k) := by
    rw [hj]
    exact ((by decide : Nat.Coprime 3 2).pow_left j).pow_right k
  have hcyc : IsCyclic P := isCyclic_of_card_dvd_prime (hcop.dvd_mul_left.mp hd)
  exact P.primeRank_le_one_of_surjective hcyc
    ((QuotientGroup.mk' (pCore 2 H)).subgroupMap Y)
    ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective Y)

/-- The source Sylow subgroup puts the kernel of the star map inside M. -/
theorem localTwoCore_le_of_sylow (H M T : Subgroup G)
    (hT : CFSG.Quasithin.Chapter1.IsSylowIn 2 T H) (hTM : T ≤ M) :
    localTwoCore H ≤ M := by
  obtain ⟨P, hP⟩ := hT
  exact (pCoreIn_le_sylow H P).trans (hP ▸ hTM)

/-- Component generation supplies a cubic element, making the rank bound an equality. -/
theorem star_threeRank_eq_one [Finite G] (H M L Y0 : Subgroup G)
    (hLH : L ≤ H) (hθ : theta (M ⊓ H) = Y0) (hcomm : L = ⁅L, Y0⁆)
    (hne : starImage H L ≠ ⊥)
    (hcard : Nat.card ((Y0.subgroupOf H) ⧸ pCore 2 (Y0.subgroupOf H)) = 3) :
    primeRank 3 (starImage H Y0) = 1 := by
  apply le_antisymm (star_threeRank_le_one H Y0 hcard)
  obtain ⟨y, hy⟩ := exists_star_cubic_of_component_action H M L Y0 hLH hθ hcomm hne
  have hsize : Nat.card (zpowers y) = 3 := (Nat.card_zpowers y).trans hy
  have hp : IsPGroup 3 (zpowers y) := IsPGroup.of_card (hsize.trans (pow_one 3).symm)
  have hn : Nontrivial (zpowers y) := Finite.one_lt_card_iff_nontrivial.mp (hsize ▸ (by decide : 1 < 3))
  let := hn
  exact (Nat.succ_le_of_lt (Group.rank_pos (G := zpowers y))).trans
    ((zpowers y).rank_le_primeRank_of_abelian_pGroup 3 hp inferInstance)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields
