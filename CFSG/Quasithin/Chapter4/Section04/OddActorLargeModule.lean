module
public import CFSG.Quasithin.Chapter4.Section04.OddActorOddCore

/-!
# Odd-core centralization for a large chosen module

The odd-core step needs only |V| > 8, not the unitary value |V| = 64.
Restrict the literal V and its perfect fixed residual to N(B), apply the
quasithin odd-core rank bound, then map the resulting commutator back to G.
This extension preserves the existing unitary interface. Its exterior
consumer has |V| = 1024 and supplies all actor hypotheses from its marking.

Source: Aschbacher--Smith, 4.4.8, printed p.620, using A.1.26 and A.1.28.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter4.Section04
variable {G : Type*} [Group G] [Finite G]

private theorem perfect_isPPerfect {H:Type*} [Group H] [Finite H]
    [Group.IsPerfect H] : IsPPerfect 2 H := by
  intro N hN hq
  let : N.Normal:=hN
  by_contra hne
  let : Nontrivial (H ⧸ N):=QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (H ⧸ N):=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (H ⧸ N):=hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (H ⧸ N) inferInstance

/-- Source 4.4.8 centralization on the actual ambient images. The original
chosen module and actor centralizer are retained throughout. -/
theorem chosen_oddNormalizer_centralizes_oddCore_of_large_module
    {K:GroupClass} {T:Sylow 2 G} {L V:Subgroup G}
    (h:Chapter12.Section02.Hypothesis1221 K T L)
    (D:Chapter12.Section02.ChosenModule T L V) (hcard:8<Nat.card V)
    (B:Subgroup G) (hBN:B≤normalizer (L:Set G))
    (hcomm:⁅B,L⁆≤L.pCoreIn 2) (hodd:Odd (Nat.card B))
    (hBV:B≤centralizer (V:Set G)) :
    ⁅V,(pPrimeCore 2 (normalizer (B:Set G))).map (normalizer (B:Set G)).subtype⁆=⊥ := by
  let N:=normalizer (B:Set G)
  let F:=oddActorResidual L B
  have hFN:F≤N:=((oddActorResidual_le L B).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hVN:V≤N:=(le_centralizer_iff.mp hBV).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨_,he,_,_⟩:=chosen_oddActorResidual_cover h D B hBN hcomm hodd hBV
  let : Group.IsPerfect F:=oddActorResidual_isPerfect L B
  let : Group.IsPerfect (F.subgroupOf N):=Group.IsPerfect.ofSurjective
    (f:=(subgroupOfEquivOfLe hFN).symm.toMonoidHom) (subgroupOfEquivOfLe hFN).symm.surjective
  let :=D.elementary
  let : IsElementaryAbelian 2 (V.subgroupOf N):=IsElementaryAbelian.subgroupOf hVN
  have heN:V.subgroupOf N=⁅V.subgroupOf N,F.subgroupOf N⁆:=by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVN,map_subgroupOf_eq_of_le hFN]
    exact he
  have hcN:8<Nat.card (V.subgroupOf N):=by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hVN).toEquiv]
  have hh:=ChapterA.large_elementary_commutator_centralizes_oddCore
    (h.simpleQTKE.quasithin.subgroup N) (F.subgroupOf N) (V.subgroupOf N) perfect_isPPerfect hcN heN
  have hm:=congrArg (Subgroup.map N.subtype) hh
  simpa only [map_commutator,map_subgroupOf_eq_of_le hVN,Subgroup.map_bot] using hm

end CFSG.Quasithin.Chapter4.Section04
