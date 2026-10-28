module
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.ActorQuotient
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.Action
public import Theory.GroupTheory.PerfectNormalizerInner.SimpleSection
/-!
# The literal residual inner action from its simple quotient

Restrict the original chosen-module action to L_A using the proved cover.
The kernel remains a two-group. Consequently, if the actual simple action
quotient cannot occur as a section of Out(K), the original residual acts
inner on K. This avoids the stronger full B-model Schreier input.

Source: the unitary specialization of Aschbacher--Smith 4.4.10, printed p.621.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section04
open ChapterE
variable {G S:Type*} [Group G] [Finite G] [Group S] [IsSimpleGroup S]
/-- A model-specific exclusion of the original simple action quotient gives the actual inner placement. -/
theorem chosen_oddNormalizer_inner_of_no_action_outer_section
    {κ:GroupClass} {T:Sylow 2 G} {L V:Subgroup G}
    (h:Chapter12.Section02.Hypothesis1221 κ T L)
    (D:Chapter12.Section02.ChosenModule T L V)
    (hfaith:L⊓centralizer (V:Set G)≤L.pCoreIn 2)
    (e:inducedAutomizer V L≃*S)
    (A:Subgroup G) (hAN:A≤normalizer (L:Set G))
    (hcomm:⁅A,L⁆≤L.pCoreIn 2) (hodd:Odd (Nat.card A)) (hAV:A≤centralizer (V:Set G))
    (K:Subgroup (normalizer (A:Set G))) (hK:IsComponent (normalizer (A:Set G)) K)
    (hno:∀U:Subgroup (MulAut.Outer K),∀g:U→*S,¬Function.Surjective g) :
    (oddActorResidual L A).subgroupOf (normalizer (A:Set G))≤
      K⊔centralizer (K:Set (normalizer (A:Set G))) := by
  obtain ⟨q,hq,hqp,_⟩:=chosen_oddActorResidual_action_surjective h D hfaith A hAN hcomm hodd hAV
  let F:=oddActorResidual L A
  let N:=normalizer (A:Set G)
  have hFN:F≤N:=((oddActorResidual_le L A).trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  let u:F.subgroupOf N≃*F:=subgroupOfEquivOfLe hFN
  let qs:F.subgroupOf N→*S:=e.toMonoidHom.comp (q.comp u.toMonoidHom)
  have hqs:Function.Surjective qs:=e.surjective.comp (hq.comp u.surjective)
  have hk:qs.ker≤q.ker.comap u.toMonoidHom:=by
    intro f hf
    change q (u f)=1
    apply e.injective
    rw [map_one]
    exact hf
  have hqu:IsPGroup 2 (q.ker.comap u.toMonoidHom):=by
    apply hqp.of_injective (u.toMonoidHom.subgroupComap q.ker)
    intro x y he
    apply Subtype.ext
    apply u.injective
    exact congrArg Subtype.val he
  let :Group.IsNilpotent qs.ker:=(hqu.to_le hk).isNilpotent
  let :Group.IsPerfect F:=oddActorResidual_isPerfect L A
  let :Group.IsPerfect (F.subgroupOf N):=Group.IsPerfect.ofSurjective
    (f:=u.symm.toMonoidHom) u.symm.surjective
  obtain ⟨_,hFK,_⟩:=chosen_oddNormalizer_component_normalization h D A hAN hcomm hodd hAV K hK
  exact perfect_le_sup_centralizer_of_no_simple_outer_section K (F.subgroupOf N) qs hqs hno hFK
end CFSG.Quasithin.Chapter4.Section04
