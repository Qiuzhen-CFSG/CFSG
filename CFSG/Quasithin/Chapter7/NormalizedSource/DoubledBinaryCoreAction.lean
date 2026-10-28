module
public import Theory.GroupTheory.CComponent.NormalPair
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPushingUp
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.CharacteristicTwo
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.FullSylowBlocks
public import Theory.GroupTheory.GeneralizedFitting.PrimeCoreNormalized

/-!
# The original core acting on the lifted component

Transport the actual normal-closure Sylow clause of C.2.3 into H, keeping
the closure inside H intersect M. Characteristic two and the quasisimple
two-core quotient permit C.2.4 on the same lifted C-component. Either the
full original Q normalizes it, or its full Sylow intersection with Q and
C.2.4(1) make it a chi-zero block. Characteristic two of the component
follows from normalization by O₂(H), rather than arbitrary subgroup
inheritance.

NonFFSourceDoubledBinaryKernel supplies every premise on the chosen
orbit. Excluding the moving block alternative and completing 7.7.8 remain
with qt-d-1222-nonff-doubled, together with the final source assembly.
Source: Aschbacher–Smith, 7.7.7–8, printed p.707; C.2.4, printed p.144.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCoreAction

private theorem closure_sylow_restrict
    {G : Type*} [Group G] [Finite G] {κ : GroupClass}
    {H Q M : Subgroup G} (h : Chapter1.RadicalExclusions.PushingUpSetup κ H Q M) :
    ChapterC.IsSylowInNormalClosure (Q.subgroupOf H) (M.subgroupOf H) := by
  let MH := M.subgroupOf H
  let QH := Q.subgroupOf H
  let e : MH ≃* M := subgroupOfEquivOfLe h.overgroup_le
  let N := normalClosure (Q.subgroupOf M : Set M)
  let NH := normalClosure (QH.subgroupOf MH : Set MH)
  have heQ : e '' (QH.subgroupOf MH : Set MH) = (Q.subgroupOf M : Set M) := by
    ext r
    constructor
    · rintro ⟨s,hs,rfl⟩; exact hs
    · intro hr
      exact ⟨⟨⟨r,h.overgroup_le r.property⟩,r.property⟩,hr,rfl⟩
  have heN : NH.map e.toMonoidHom = N := by
    rw [map_normalClosure _ _ e.surjective]
    change normalClosure (e '' (QH.subgroupOf MH : Set MH)) = N
    rw [heQ]
  let eN : NH ≃* N.map M.subtype :=
    ((e.subgroupMap NH).trans (MulEquiv.subgroupCongr heN)).trans
      (N.equivMapOfInjective M.subtype M.subtype_injective)
  obtain ⟨S,hS⟩ := h.sylow
  let T : Sylow 2 NH := S.mapSurjective (f := eN.symm.toMonoidHom) eN.symm.surjective
  refine ⟨T,?_⟩
  apply map_injective H.subtype_injective
  rw [map_subgroupOf_eq_of_le h.radical_le]
  change (((((S : Subgroup (N.map M.subtype)).map eN.symm.toMonoidHom).map NH.subtype).map MH.subtype).map H.subtype) = Q
  rw [map_map,map_map,map_map]
  apply Eq.trans ?_ hS
  congr 1
  ext x
  exact congrArg Subtype.val (eN.apply_symm_apply x)

/-- C.2.4 applies to the lifted C-component and the full original Q. A moved
component is a chi-zero block and its original Sylow is contained in Q. -/
theorem original_core_component_alternative
    {G : Type*} [Group G] [Finite G] {H Q M : Subgroup G}
    (h : Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple H Q M)
    (hc : HasCharacteristicTwo H) (hf : generalizedFitting H = pCore 2 H)
    (C : Subgroup H) (hC : C.IsCComponent)
    [IsQuasisimple (C ⧸ pCore 2 C)] (hout : ¬ C ≤ M.subgroupOf H) :
    generalizedFitting C = pCore 2 C ∧
      ((Q.subgroupOf H ≤ normalizer (C : Set H)) ∨
        (ChapterC.IsChiZeroBlock C ∧ ∃ P : Sylow 2 C,
          (P : Subgroup C).map C.subtype = Q.subgroupOf H ⊓ C)) := by
  have hfit := generalizedFitting_eq_pCore_of_normalized_by_pCore C hf (hC.pCore_le_normalizer 2)
  refine ⟨hfit,?_⟩
  rcases ChapterC.Section02Source.sylow_intersection_or_normalizes_of_characteristicTwo
    h.sqtk (Q.subgroupOf H) (M.subgroupOf H) C h.radical h.characteristic_control
    (closure_sylow_restrict h) hC hc with ⟨P,hP⟩ | hn
  · right
    have ho : pPrimeCore 2 H = ⊥ := pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hc
    exact ⟨ChapterC.CatalogueFullSylow.constrained_component_chiZero_of_full_sylow
      h.sqtk (Q.subgroupOf H) (M.subgroupOf H) C h.radical h.characteristic_control hC
      ho hfit hout P (hP.trans_le inf_le_left),P,hP⟩
  · exact Or.inl hn

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCoreAction
