module
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.JankoThree
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.ActionSection
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.OddCentralizer
public import Theory.GroupTheory.GeneralizedFitting.OddComponentCentralizer
public import Theory.GroupTheory.SimpleSectionSolvableReduction.Model
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# Excluding J₃ in the original unitary odd-normalizer argument

The actual residual L_A has the G₂(2)′ chosen-module quotient. The certified
J₃ Sylow bound excludes that simple section from the outer automorphism group
of its original central cover. Thus L_A acts inner on the selected component.
The source uniqueness argument puts the chosen module in that component,
forces its centralizer to have odd order, and puts L_A itself in the component.
Its simple G₂(2)′ quotient would then be a section of J₃, contradicting the
absence of seven from the certified J₃ order.

The final consumer chooses the component with the complete KnownSimple A/B
source theorems and removes J₃ from its model alternatives. The earlier genuine
uniqueness of the odd-actor residual remains explicit. No full B-model Schreier
input, component normality or additional geometric hypothesis is required.

Source: Aschbacher–Smith, the unitary specialization of 4.4.10–12 and 4.4.3,
printed pp.621–623; its original 13.3.16 application, pp.895–896.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section04
open ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- The actual selected component cannot have J₃ central quotient in the
original unitary action. The central covering kernel is retained throughout. -/
theorem selected_jankoThree_false_of_original_unitary
    {κ : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 κ T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hfaith : L ⊓ centralizer (V : Set G) ≤ L.pCoreIn 2)
    (e : inducedAutomizer V L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hunique : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (hmodel : Nonempty (K ⧸ center K ≃* Sporadic.Janko3.Model)) : False := by
  let S := commutator (Atlas.G2.Model (ZMod 2))
  let : IsSimpleGroup S := Atlas.G2.isSimple_commutator_binary
  let : Group.IsPerfect S := by
    change Group.IsPerfect Atlas.G2.LieAutomorphismExtensions.BinaryDerived
    rw [Atlas.G2.LieAutomorphismExtensions.binaryDerived_eq]
    exact Atlas.G2.BinaryException.H_isPerfect
  have hinner := chosen_oddNormalizer_inner_of_no_action_outer_section h D hfaith e
    A hAN hcomm hodd hAV K hK
    (fun U f hf => selected_jankoThree_no_binaryDerived_outer_section A K hK hmodel U f hf)
  have hVK := chosen_oddNormalizer_module_le_of_component_inner_action
    h D A hAN hcomm hodd hAV hunique K houtK hinner
  have ho := chosen_oddNormalizer_component_centralizer_odd h D hfaith
    A hAN hcomm hodd hAV hunique hout K hK houtK hVK
  let N := normalizer (A : Set G)
  let F := oddActorResidual L A
  have hFN : F ≤ N := ((oddActorResidual_le L A).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  let : Group.IsPerfect F := oddActorResidual_isPerfect L A
  let : Group.IsPerfect (F.subgroupOf N) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hFN).symm.toMonoidHom)
    (subgroupOfEquivOfLe hFN).symm.surjective
  have hFK := hK.perfect_actor_le_of_odd_centralizer ho (F.subgroupOf N) hinner
  obtain ⟨q,hq,_,_⟩ := chosen_oddActorResidual_action_surjective h D hfaith A hAN hcomm hodd hAV
  let u : F.subgroupOf N ≃* F := subgroupOfEquivOfLe hFN
  let v : (F.subgroupOf N).subgroupOf K ≃* F.subgroupOf N := subgroupOfEquivOfLe hFK
  let f : (F.subgroupOf N).subgroupOf K →* S :=
    e.toMonoidHom.comp (q.comp (u.toMonoidHom.comp v.toMonoidHom))
  have hf : Function.Surjective f := e.surjective.comp (hq.comp (u.surjective.comp v.surjective))
  let : CommGroup (center K) := IsMulCommutative.instCommGroup
  let m : Group.SolvableKernelModel K Sporadic.Janko3.Model := {
    kernel := center K
    normal := inferInstance
    solvable := inferInstance
    quotientEquiv := hmodel.some }
  obtain ⟨W,g,hg⟩ := m.simple_section (Group.IsPerfect.not_isSolvable S)
    ((F.subgroupOf N).subgroupOf K) f hf
  have hd := (Subgroup.card_dvd_of_surjective g hg).trans W.card_subgroup_dvd_card
  have h7 : 7 ∣ Nat.card S := by
    change 7 ∣ Nat.card Atlas.G2.LieAutomorphismExtensions.BinaryDerived
    rw [Atlas.G2.LieAutomorphismExtensions.card_binaryDerived]
    norm_num
  have h7J := h7.trans hd
  rw [Sporadic.Janko3.model_card] at h7J
  norm_num at h7J

/-- Select the original component using the full proved A/B source and exclude
J₃ by its actual residual action; no universal outer-solvability input remains. -/
theorem chosen_oddNormalizer_exists_component_without_jankoThree
    {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : Chapter12.Section02.ChosenModule T L V) (hcard : Nat.card V = 64)
    (hfaith : L ⊓ centralizer (V : Set G) ≤ L.pCoreIn 2)
    (e : inducedAutomizer V L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAN : A ≤ normalizer (L : Set G)) (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2)
    (hodd : Odd (Nat.card A)) (hAV : A ≤ centralizer (V : Set G))
    (hunique : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K, V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) ∧
      V.subgroupOf (normalizer (A : Set G)) ≤ normalizer (K : Set (normalizer (A : Set G))) ∧
      ¬ Nonempty (K ⧸ center K ≃* Sporadic.Janko3.Model) := by
  obtain ⟨K,hK,hm,houtK,hcore,hmodel,hFK,hVK⟩ :=
    chosen_oddNormalizer_exists_theoremB_component
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremB_knownSimple)
      h D hcard A hne hAN hcomm hodd hAV hunique hout
  exact ⟨K,hK,hm,houtK,hcore,hmodel,hFK,hVK,
    selected_jankoThree_false_of_original_unitary h D hfaith e
      A hAN hcomm hodd hAV hunique hout K hK houtK⟩

end CFSG.Quasithin.Chapter4.Section04
