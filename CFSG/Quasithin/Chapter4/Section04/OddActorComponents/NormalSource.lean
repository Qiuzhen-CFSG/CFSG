module
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.InnerPlacement
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.OddCentralizer
public import Theory.GroupTheory.GeneralizedFitting.OddComponentCentralizer
/-!
# The original normal component and residual placement

Compose the actual selected component, inner residual action, canonical
prime projection and odd-centralizer argument. The chosen V and residual
L_A lie in the same normal component of N(A), whose centralizer is the
literal odd core. The sharper A.3.8 orbit catalogue is unnecessary for this
specialization because the genuine unique two-local overgroup of L_A is
available.

Source: the unitary specialization of Aschbacher--Smith 4.4.10--11,
printed p.621. Earlier A/B, the explicitly unfinished B-model outer input,
and the genuine pushing-up uniqueness remain visible inputs. This is not
an assertion of the final 4.4.3 normalizer containment.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section04
universe u
variable {G:Type u} [Group G] [Finite G]
/-- Actual earlier source inputs produce the normal component required by the subsequent model inspection. -/
theorem chosen_oddNormalizer_exists_normal_component
    {κ:GroupClass.{u}} {T:Sylow 2 G} {L V:Subgroup G}
    (hA:∀(X:Type u)[Group X][Finite X],ChapterA.Section02.TheoremA κ X)
    (hB:∀(X:Type u)[Group X][Finite X],ChapterA.Section02.TheoremB κ X)
    (hOuter:ChapterA.Section03.SourceComponents.TheoremBOuter.SourceInput.{u})
    (h:Chapter12.Section02.Hypothesis1221 κ T L)
    (D:Chapter12.Section02.ChosenModule T L V) (hcard:Nat.card V=64)
    (hfaith:L⊓centralizer (V:Set G)≤L.pCoreIn 2)
    (A:Subgroup G) [IsMulCommutative A] (hne:A≠⊥)
    (hAN:A≤normalizer (L:Set G)) (hcomm:⁅A,L⁆≤L.pCoreIn 2)
    (hodd:Odd (Nat.card A)) (hAV:A≤centralizer (V:Set G))
    (hunique:UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L:Set G)))
    (hout:¬normalizer (A:Set G)≤normalizer (L:Set G)) :
    ∃K:Subgroup (normalizer (A:Set G)),
      IsComponent (normalizer (A:Set G)) K ∧ K.Normal ∧
      ⁅K,V.subgroupOf (normalizer (A:Set G))⁆=K ∧
      ¬K.map (normalizer (A:Set G)).subtype≤normalizer (L:Set G) ∧
      pCore 2 K=⊥ ∧ ChapterA.Section02.IsTheoremBModel (K⧸center K) ∧
      V≤K.map (normalizer (A:Set G)).subtype ∧
      oddActorResidual L A≤K.map (normalizer (A:Set G)).subtype ∧
      centralizer (K:Set (normalizer (A:Set G)))=pPrimeCore 2 (normalizer (A:Set G)) := by
  obtain ⟨K,hK,hm,houtK,hcore,hmodel,hi,_⟩:=chosen_oddNormalizer_exists_inner_component
    hA hB hOuter h D hcard A hne hAN hcomm hodd hAV hunique hout
  have hv:=chosen_oddNormalizer_module_le_of_component_inner_action
    h D A hAN hcomm hodd hAV hunique K houtK hi
  have ho:=chosen_oddNormalizer_component_centralizer_odd
    h D hfaith A hAN hcomm hodd hAV hunique hout K hK houtK hv
  let N:=normalizer (A:Set G)
  let F:=oddActorResidual L A
  have hFN:F≤N:=((oddActorResidual_le L A).trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  let :Group.IsPerfect F:=oddActorResidual_isPerfect L A
  let :Group.IsPerfect (F.subgroupOf N):=Group.IsPerfect.ofSurjective
    (f:=(subgroupOfEquivOfLe hFN).symm.toMonoidHom) (subgroupOfEquivOfLe hFN).symm.surjective
  have hFK:F≤K.map N.subtype:=by
    have hh:=map_mono (f:=N.subtype) (hK.perfect_actor_le_of_odd_centralizer ho (F.subgroupOf N) hi)
    rwa [map_subgroupOf_eq_of_le hFN] at hh
  exact ⟨K,hK,hK.normal_of_odd_centralizer ho,hm,houtK,hcore,hmodel,hv,hFK,
    hK.centralizer_eq_oddCore_of_odd_centralizer ho⟩
end CFSG.Quasithin.Chapter4.Section04
