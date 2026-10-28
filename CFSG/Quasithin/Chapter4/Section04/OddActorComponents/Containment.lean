module
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.Action
public import Theory.GroupTheory.CentralProductPrimeProjection
/-!
# Chosen-module containment from the actual inner component action

The prime projection of the original V onto the component centralizer is
normalized by L_A, since L_A normalizes V and the component. The genuine
unique maximal-two-local overgroup of L_A forces that projection to vanish:
otherwise its normalizer would contain the component outside N(L).

Source: Aschbacher--Smith 4.4.10(2), printed p.621. The remaining inner-action
input is owned by the Theorem B model automorphism producer; neither chosen
module invariance under all of N(L) nor an orbit-two premise is required.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section04
variable {G:Type*} [Group G] [Finite G]

/-- The literal inner-action output places the same source V in the selected K. -/
theorem chosen_oddNormalizer_module_le_of_component_inner_action
    {κ:GroupClass} {T:Sylow 2 G} {L V:Subgroup G}
    (h:Chapter12.Section02.Hypothesis1221 κ T L)
    (D:Chapter12.Section02.ChosenModule T L V)
    (A:Subgroup G) (hAN:A≤normalizer (L:Set G))
    (hcomm:⁅A,L⁆≤L.pCoreIn 2) (hodd:Odd (Nat.card A))
    (hAV:A≤centralizer (V:Set G))
    (hunique:UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L:Set G)))
    (K:Subgroup (normalizer (A:Set G)))
    (hout:¬K.map (normalizer (A:Set G)).subtype≤normalizer (L:Set G))
    (hinner:(oddActorResidual L A).subgroupOf (normalizer (A:Set G))≤
      K⊔centralizer (K:Set (normalizer (A:Set G)))) :
    V≤K.map (normalizer (A:Set G)).subtype := by
  let N:=normalizer (A:Set G)
  let F:=oddActorResidual L A
  let J:=K.map N.subtype
  have hFN:F≤N:=((oddActorResidual_le L A).trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  have hC:(centralizer (K:Set N)).map N.subtype≤centralizer (J:Set G):=by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact congrArg Subtype.val (hx y hy)
  have hi:F≤J⊔centralizer (J:Set G):=by
    have hh:=map_mono (f:=N.subtype) hinner
    rw [map_subgroupOf_eq_of_le hFN,Subgroup.map_sup] at hh
    exact hh.trans (sup_le_sup le_rfl hC)
  obtain ⟨_,_,hc,_⟩:=chosen_oddActorResidual_cover h D A hAN hcomm hodd hAV
  let :=D.elementary
  exact binary_subgroup_le_of_inner_product_uniqueness J V F (normalizer (L:Set G))
    (IsElementaryAbelian.isPGroup 2 V) (hc.trans (pCoreIn_le 2 F))
    (hi.trans (sup_le J.le_normalizer (Subgroup.centralizer_le_normalizer _)))
    (((oddActorResidual_le L A).trans inf_le_left).trans D.normalizes)
    hi hunique.2.2 hout
end CFSG.Quasithin.Chapter4.Section04
