module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.SourceChiefImages
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.SimpleImage
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison

/-!
# Comparing the original marked component with a chief action

The image of the selected component is precisely the generalized Fitting
subgroup of its faithful noncentral chief action. Both that image and K̂
are quotients of the same original K*. Their simple central quotients are
therefore canonically isomorphic, retaining the literal action homomorphism.
This supplies the comparison input for the model exclusions in13.5.21.
Source: Aschbacher–Smith13.5.21, printed pp.923–924.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
open Section08.Source Configuration
universe u

/-- The original component image is the quasisimple generalized Fitting subgroup. -/
theorem image_component_eq_fitting
    {E W : Type*} [Group E] [Finite E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (L : Subgroup E) [L.Normal] [IsQuasisimple L]
    (hn : ¬ L ≤ ρ.ker) [IsQuasisimple (generalizedFitting (actionImage ρ))] :
    actionSubgroup ρ L = generalizedFitting (actionImage ρ) := by
  let M := actionSubgroup ρ L
  let f := actionHom ρ
  have hMbot : M ≠ ⊥ := by
    intro hbot
    apply hn
    have hm : L ≤ f.ker := (Subgroup.map_eq_bot_iff L).mp hbot
    simpa only [action_kernel_eq] using hm
  let : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).mpr hMbot
  let : IsQuasisimple M := IsQuasisimple.of_surjective
    (f.subgroupMap L) (f.subgroupMap_surjective L)
  let : M.Normal := Subgroup.Normal.map inferInstance f ρ.asGroupHom.rangeRestrict_surjective
  have hM : IsComponent (actionImage ρ) M := ⟨(inferInstance : M.Normal).isSubnormal,inferInstance⟩
  exact hM.eq_of_le
    ⟨(inferInstance : (generalizedFitting (actionImage ρ)).Normal).isSubnormal,inferInstance⟩
    (component_le_generalizedFitting _ _ hM)

variable {G : Type u} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (K : Subgroup G) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
  (s : Selected D K) [(componentCentralizer s h).Normal] [(component D K).Normal]

/-- Literal marked comparison for every noncentral chief action with its proved B.4 hypotheses. -/
theorem source_chief_component_comparison
    (U N : Subrepresentation (representation D K h))
    (hn : ¬ component D K ≤ (chiefRepresentation D K h U N).ker)
    (hyp : Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.B4Hypotheses
      KnownSimple.IsKnownSimple (imageRepresentation (chiefRepresentation D K h U N))) :
    Nonempty (Khat s h ≃*
      (generalizedFitting (actionImage (chiefRepresentation D K h U N)) ⧸
        center (generalizedFitting (actionImage (chiefRepresentation D K h U N))))) := by
  let ρ := chiefRepresentation D K h U N
  let C := component D K
  let F := generalizedFitting (actionImage ρ)
  let e : C ≃* starImage D.H K := subgroupOfEquivOfLe le_sup_left
  let : IsQuasisimple (starImage D.H K) := s.quasisimple
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv e.symm
  let : IsQuasisimple F := hyp.quasisimple
  let : IsSimpleGroup (F ⧸ center F) := IsQuasisimple.simple
  let : Nontrivial F := (QuotientGroup.mk'_surjective (center F)).nontrivial
  have he : actionSubgroup ρ C = F := image_component_eq_fitting ρ C hn
  let f : starImage D.H K →* F :=
    ((MulEquiv.subgroupCongr he).toMonoidHom.comp
      ((actionHom ρ).subgroupMap C)).comp e.symm.toMonoidHom
  have hf : Function.Surjective f :=
    ((MulEquiv.subgroupCongr he).surjective.comp
      ((actionHom ρ).subgroupMap_surjective C)).comp e.symm.surjective
  exact ⟨(KhatEquiv s h).trans (IsQuasisimple.centralQuotientEquiv f hf)⟩
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
