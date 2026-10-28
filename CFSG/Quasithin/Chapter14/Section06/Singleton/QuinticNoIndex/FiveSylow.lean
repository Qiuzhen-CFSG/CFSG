module
public import CFSG.Quasithin.Chapter14.Section06.Singleton.QuinticNoIndex.Wreath
public import Theory.SpecificGroups.PSL2.SixteenWreathOrder
public import Theory.GroupTheory.SylowSubnormalIntersectionIndex

/-!
# Sylow-five transport in the no-index strict closure

The faithful marked action embeds Mc/O₂(Mc) into the actual PSL₂(16)
automorphism wreath, whose order has five-part 25. The original residual
already has order 25 in J/O₂(J), so J has index prime to five in Mc.
Subnormal Sylow intersection then makes each actual PSL₂(16) component
meet J in order divisible by five, through the literal subgroup maps.

This removes the factor-join index and full-wreath surjectivity assumptions
from this Sylow step. Source applies it to the original singleton reduction.
The component intersections still need alignment with the original factor
residuals, and the no-index normalizer and final outer contradiction remain
open. Source: Aschbacher--Smith 14.6.15, printed pp.1033--1034.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open OddNormalizer Chapter1 Chapter1.XiEmbedding
namespace Singleton.QuinticNoIndex
open SourcePairCompatibility.QuinticGeometryParallel
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
variable (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation)
    (π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index)
    (w : SourcePairCompatibility.QuinticOuterAction a f d π)




include hG hempty hM hu hmany hcard e hab hJ hs w

/-- The strict branch already contains a full Sylow five-subgroup of Mc.
Only the faithful marked wreath embedding and original residual order 25
are needed; no full wreath image or factor-join index is assumed. -/
theorem source_quintic_strict_outside_index_primeTo_five
    (hne : residualClosure J Mc ≠ residual J) : ¬5 ∣ J.relIndex Mc := by
  obtain ⟨L,_,_,_,_,_,_,_,_,_,_,s,_,_,_,hmarked⟩ :=
    source_quintic_strict_closure_wreath hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π w hne
  obtain ⟨_,_,_,_,ρ,hρ,_,_⟩ := hmarked
  have hnc : ¬125 ∣ Nat.card Mc := by
    intro hd
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := Mc)).exists_card_eq
    rw [←(pCore 2 Mc).card_mul_index,index_eq_card,hn] at hd
    have hquot := ((by decide : Nat.Coprime 125 2).pow_right n).dvd_of_dvd_mul_left hd
    exact Theory.PSL2.SixteenWreathComponents.not_five_cube_dvd_card
      (hquot.trans (card_dvd_of_injective ρ hρ))
  have hJMc : J ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hu)
  have h25 : 25 ∣ Nat.card (J.subgroupOf Mc) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hJMc).toEquiv]
    have hd := (pResidual 2 (J ⧸ pCore 2 J)).card_subgroup_dvd_card
    rw [source_quintic_residual_plane_card hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π w] at hd
    exact hd.trans (card_quotient_dvd_card (pCore 2 J))
  intro hi
  change 5 ∣ (J.subgroupOf Mc).index at hi
  apply hnc
  have hd := Nat.mul_dvd_mul h25 hi
  rwa [(J.subgroupOf Mc).card_mul_index] at hd

/-- Every actual PSL₂(16) component meets J in order divisible by five.
The intersection is transported through the literal subgroup inclusion in Mc,
using the no-index Sylow-five conclusion above. -/
theorem source_quintic_strict_component_intersection_five_dvd
    (hne : residualClosure J Mc ≠ residual J)
    {K : Subgroup G} (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hmodel : ClassicalGroup.IsPSL
      ((K.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 2 16) :
    5 ∣ Nat.card (K ⊓ J : Subgroup G) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨ek⟩ := binary_component_equiv (m := 4) hmodel
  have hd : 5 ∣ Nat.card (K.subgroupOf Mc) := by
    have hi : 5 ∣ Nat.card ((K.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) := by
      rw [Nat.card_congr ek.toEquiv]
      exact Theory.PSL2.SixteenWreathComponents.five_dvd_card
    exact hi.trans (card_map_dvd _ _)
  have hh := prime_dvd_intersection_of_subnormal_of_primeTo_index
    (J.subgroupOf Mc) (K.subgroupOf Mc)
    (source_quintic_strict_outside_index_primeTo_five hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π w hne) hK.subnormal hd
  have hJMc : J ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hu)
  have he : ((K.subgroupOf Mc) ⊓ (J.subgroupOf Mc)).map Mc.subtype = K ⊓ J := by
    rw [Subgroup.map_inf _ _ _ Mc.subtype_injective,
      map_subgroupOf_eq_of_le hKM,map_subgroupOf_eq_of_le hJMc]
  rwa [←he,card_map_of_injective Mc.subtype_injective]

end Singleton.QuinticNoIndex
end CFSG.Quasithin.Chapter14.Section06
