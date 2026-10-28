module
public import CFSG.Quasithin.Chapter4.Section04.OddActorReduction
-- Internal companion: retain the sealed residual definition and export its perfection.
import all CFSG.Quasithin.Chapter4.Section04.OddActorResidual
public import CFSG.Quasithin.ChapterA.Section01.RankActions.LargeElementary

/-!
# The chosen unitary module centralizes the actual odd-normalizer odd core

Restrict the original chosen V and the fixed residual L_B to N_G(B).
The covering theorem retains V=[V,L_B], and the finite solvable residual
is perfect. Since V has order 64, A.1.28 bounds every odd-prime core rank;
A.1.26 then centralizes the full odd core. The independent earlier
pushing-up uniqueness theorem is used only to place that core in M.
No strong quasithinness or component classification is assumed here.

Source: Aschbacher--Smith, Lemma 4.4.8, printed p.620, in the unitary
six-dimensional case of Theorem 4.4.3.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter4.Section04
variable {G:Type*} [Group G] [Finite G]

/-- The actual fixed residual is perfect, without modifying the sealed definition. -/
theorem oddActorResidual_isPerfect (L B:Subgroup G) :
    Group.IsPerfect (oddActorResidual L B) :=
  Group.IsPerfect.map (L⊓centralizer (B:Set G)).subtype

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
theorem chosen_oddNormalizer_centralizes_oddCore
    {K:GroupClass} {T:Sylow 2 G} {L V:Subgroup G}
    (h:Chapter12.Section02.Hypothesis1221 K T L)
    (D:Chapter12.Section02.ChosenModule T L V) (hcard:Nat.card V=64)
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
    rw [Nat.card_congr (subgroupOfEquivOfLe hVN).toEquiv,hcard]
    decide
  have hh:=ChapterA.large_elementary_commutator_centralizes_oddCore
    (h.simpleQTKE.quasithin.subgroup N) (F.subgroupOf N) (V.subgroupOf N) perfect_isPPerfect hcN heN
  have hm:=congrArg (Subgroup.map N.subtype) hh
  simpa only [map_commutator,map_subgroupOf_eq_of_le hVN,Subgroup.map_bot] using hm

/-- The odd core lies in M once the independent genuine uniqueness result
for L_B is available. This is not a normalizer-containment assumption. -/
theorem chosen_oddNormalizer_oddCore_le_of_uniqueness
    {K:GroupClass} {T:Sylow 2 G} {L V M:Subgroup G}
    (h:Chapter12.Section02.Hypothesis1221 K T L)
    (D:Chapter12.Section02.ChosenModule T L V) (hcard:Nat.card V=64)
    (B:Subgroup G) (hBN:B≤normalizer (L:Set G))
    (hcomm:⁅B,L⁆≤L.pCoreIn 2) (hodd:Odd (Nat.card B))
    (hBV:B≤centralizer (V:Set G))
    (hunique:UniqueMaximalOvergroup (oddActorResidual L B) M) :
    (pPrimeCore 2 (normalizer (B:Set G))).map (normalizer (B:Set G)).subtype≤M := by
  have hc:=chosen_oddNormalizer_centralizes_oddCore h D hcard B hBN hcomm hodd hBV
  have hNV:normalizer (V:Set G)≤M:=by
    let :=D.elementary
    exact normalizer_le_of_unique_maximalTwoLocal hunique.2.2
      (IsElementaryAbelian.isPGroup 2 V) D.ne_bot
      (((oddActorResidual_le L B).trans inf_le_left).trans D.normalizes)
  exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
    ((Subgroup.centralizer_le_normalizer _).trans hNV)
end CFSG.Quasithin.Chapter4.Section04
