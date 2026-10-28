module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Core.Models
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.EightQuotientRank
public import Theory.ElementaryAbelian.PrimeRankCard

/-!
# The moved subgroup in the actual component quotient

The natural summand and its dual polar hyperplane are disjoint and have
orders 2^n and 2^(n−1). Their product U therefore has order 2^(2n−1).
For the ordinary component K identified at the pure point, the kernel of
U → K/O₂(K) is exactly U ∩ Z(K) = ⟨w⟩, of order two. The literal quotient
image is elementary of order 2^(2n−2), giving the source rank obstruction.

The final application supplies the component containment and center identity
from the original chosen-module data and ambient Sylow. Model exclusion and
the dimension-four Sylow argument remain with `qt-d-double-natural-pure-fusion`.
Source: Aschbacher--Smith, 12.1.6, printed p.791, and H.9.1(3), p.390.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

theorem pure_moving_card
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    Nat.card (B.naturalSummand ⊔ S.pureDualHyperplane w hp : Subgroup G) = 2 ^ (2*n-1) := by
  have hn : (binarySubgroup S.setup.natural).map
      (componentOrbit V (T : Subgroup G)).subtype = B.naturalSummand := by
    ext x
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact (B.mem_naturalSummand v).mpr ((S.natural_marking v).mp hv)
    · intro hx
      let v : componentOrbit V (T : Subgroup G) := ⟨x,B.naturalSummand_le hx⟩
      exact ⟨v,(S.natural_marking v).mpr ((B.mem_naturalSummand v).mp hx),rfl⟩
  have hnc : Nat.card B.naturalSummand = 2 ^ n := by
    rw [←hn,card_map_of_injective (componentOrbit V (T : Subgroup G)).subtype_injective,
      binarySubgroup_card,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      S.setup.naturalCoordinates.finrank_eq]
    simp only [BinaryLinear.OuterCyclic.Space,Module.finrank_pi,Fintype.card_fin]
  have hdc : Nat.card (S.pureDualHyperplane w hp) = 2 ^ (n-1) := by
    change Nat.card ((binarySubgroup (S.setup.dualHyperplane
      ⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩)).map
      (componentOrbit V (T : Subgroup G)).subtype) = _
    rw [card_map_of_injective (componentOrbit V (T : Subgroup G)).subtype_injective,
      binarySubgroup_card,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      S.setup.dualHyperplane_finrank _ hw]
  have hd : Disjoint B.naturalSummand (S.pureDualHyperplane w hp) :=
    (disjoint_iff.mpr B.naturalSummand_inf_dualSummand).mono_right
      (S.pureDualHyperplane_le_dualSummand w hp)
  have hc : S.pureDualHyperplane w hp ≤ centralizer (B.naturalSummand : Set G) := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨y,B.naturalSummand_le hy⟩ : componentOrbit V (T : Subgroup G))
      ⟨x,B.dualSummand_le (S.pureDualHyperplane_le_dualSummand w hp hx)⟩)
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (hc.trans (Subgroup.centralizer_le_normalizer _)) hd, hnc,hdc,←pow_add]
  congr 1
  have := S.setup.degree
  omega

/-- The image in the actual component quotient has precisely the source
rank 2n−2. Its kernel is the original point line, not an unspecified center. -/
theorem pure_component_quotient_card_rank
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0)
    (K : Subgroup (B.pointCentralizer w))
    (hX : (B.pointResidual w).subgroupOf (B.pointCentralizer w) ≤ K)
    (hU : B.naturalSummand ⊔ S.pureDualHyperplane w hp ≤ K.map (B.pointCentralizer w).subtype)
    (hc : center K = pCore 2 K) :
    let A := ((B.naturalSummand ⊔ S.pureDualHyperplane w hp).subgroupOf
      (B.pointCentralizer w)).subgroupOf K
    IsElementaryAbelian 2 (A.map (QuotientGroup.mk' (pCore 2 K))) ∧
      Nat.card (A.map (QuotientGroup.mk' (pCore 2 K))) = 2 ^ (2*n-2) ∧
      2*n-2 ≤ primeRank 2 (K ⧸ pCore 2 K) := by
  let H := B.pointCentralizer w
  let U := B.naturalSummand ⊔ S.pureDualHyperplane w hp
  let j : K →* G := H.subtype.comp K.subtype
  have hj : Function.Injective j := H.subtype_injective.comp K.subtype_injective
  let A := U.comap j
  have hAm : A.map j = U := by
    apply map_comap_eq_self
    simpa only [j,MonoidHom.range_comp,range_subtype] using hU
  have hAW : U ≤ componentOrbit V (T : Subgroup G) :=
    sup_le B.naturalSummand_le ((S.pureDualHyperplane_le_dualSummand w hp).trans B.dualSummand_le)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (inclusion hAW) (inclusion_injective hAW)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.comap_of_injective j hj U
  let q := QuotientGroup.mk' (pCore 2 K)
  let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  have hAc : Nat.card A = 2^(2*n-1) := by
    rw [← card_map_of_injective hj,hAm]
    exact S.pure_moving_card w hw hp
  have hk : Nat.card (A ⊓ q.ker : Subgroup K) = 2 := by
    rw [←card_map_of_injective hj,map_inf _ _ _ hj,hAm,QuotientGroup.ker_mk',←hc]
    rw [show (center K).map j = ((center K).map K.subtype).map H.subtype from (map_map _ _ _).symm]
    rw [S.pure_moving_center_intersection w hw hp K hX hU,Nat.card_zpowers]
    exact orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (w : G) w.property)
      (fun he => hw (Subtype.ext he))
  have hi := IsElementaryAbelian.card_inf_ker_mul_card_map A q
  rw [hk,hAc] at hi
  have he : 2*n-1 = (2*n-2)+1 := by have := S.setup.degree; omega
  rw [he,pow_succ] at hi
  have hcard : Nat.card (A.map q) = 2^(2*n-2) := by omega
  change IsElementaryAbelian 2 (A.map q) ∧ Nat.card (A.map q) = 2^(2*n-2) ∧ _
  refine ⟨inferInstance,hcard,?_⟩
  have hr : primeRank 2 (A.map q) = 2*n-2 := by
    have hh := IsElementaryAbelian.card_eq_pow_primeRank (p := 2) (A.map q)
    rw [hcard] at hh
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2) hh).symm
  rw [←hr]
  exact primeRank_subgroup_le _ _

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original marked pure point forces the component quotient to have
two-rank at least 2n−2. All local containment and central-kernel premises
are discharged by the original chosen-module hypotheses. -/
theorem doubleNatural_pure_component_quotient_rank_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, B.NonsingularCentralizers →
      S.MarkedAmbientSylow D.sylow_normalizes_component →
      ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ∀ K : Subgroup (B.pointCentralizer w), IsComponent (B.pointCentralizer w) K →
        2*n-2 ≤ primeRank 2 (K ⧸ pCore 2 K) := by
  let := D.doubledOrbit_elementary h
  intro S hns hs w hw hp hfix K hK
  obtain ⟨_,hX,hU⟩ := D.doubleNatural_pure_component_identification_of_many
    h hmany B S hns hs w hw hp hfix K hK
  let := hK.2
  have hc : center K = pCore 2 K := IsQuasisimple.center_eq_pCore
    (hK.1.pPrimeCore_eq_bot (D.doubleNatural_pure_oddCore_eq_bot_of_many h hmany B S hns w hw hp) K)
  exact (S.pure_component_quotient_card_rank w hw hp K hX hU hc).2.2

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
