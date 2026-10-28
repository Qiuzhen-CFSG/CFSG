module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramOriginalException
public import CFSG.Quasithin.Chapter14.Section02.ExceptionalDiagram.Source
public import Theory.SpecificGroups.PSL3.LinearThreeFieldTransport.Diagram
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.Basic

/-!
# Original diagram residual contains the source two-core

The maximal two-core already controls every larger field. On failure,
the cubic-cover proof supplies the actual PSL₃(4) quotient. The canonical
Mc action, with its inner range and literal normalizer placement, is then
transported between four-element fields and fed to the exceptional source
branch. Component normality in Mc is exactly the preceding source9 input.

Source: Aschbacher--Smith 14.2.12--13, printed p.984.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
 theorem source_linear_diagram_residual_twoCore_le
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hn : 1 < generationParameter H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤)
    {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = 2^f) (hf : 1 < f)
    (mark : sourceImage ((H ⊓ M).subgroupOf H) K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (hmark : (componentOverlap ((H ⊓ M).subgroupOf H) K).map mark.toMonoidHom =
      Matrix.PSL3.LinearThree.borel F)
    (hmove : MovesDiagram ((H ⊓ M).subgroupOf H) K
      (T.subtype hH.1.1.2 : Subgroup H) mark
      (Matrix.PSL3.LinearThree.pointParabolic F) (Matrix.PSL3.LinearThree.lineParabolic F))
    (hMc : ((K.map H.subtype).subgroupOf Mc).Normal) :
    (sourceResidual M Mc).pCoreIn 2 ≤ (T : Subgroup G) ⊓ normalizer
      ((markedParabolicResidual ((H ⊓ M).subgroupOf H) K mark
        (Matrix.PSL3.LinearThree.pointParabolic F)).map H.subtype : Set G) := by
  let L := (markedParabolicResidual ((H ⊓ M).subgroupOf H) K mark
    (Matrix.PSL3.LinearThree.pointParabolic F)).map H.subtype
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  by_cases hMS : M.pCoreIn 2 ≤ S
  · have hMY : M ≤ normalizer (sourceResidual M Mc : Set G) :=
      (normal_subgroupOf_iff_le_normalizer (sourceResidual_le _ _)).mp (residualY_normal M Mc)
    exact (pCoreIn_mono_of_normalizes (sourceResidual_le M Mc) hMY).trans hMS
  · obtain ⟨hf2,hm⟩ := source_linear_diagram_exception_of_core_not_normalized
      hG T hempty hM hu hmany hcard e H hH hn K hK hqK hgen hF hf mark hmark hMS
    subst f
    obtain ⟨ρ,hinner,hswap,hplace⟩ := source_linear_diagram_Mc_action
      hG T hempty hM hu hmany hcard e H hH hn K hK hqK hgen hF hf mark hmark hmove hMc
    let s := (Matrix.PSL3.ExceptionalFourCover.fieldEquiv F (by simpa using hF)).symm
    let d := Atlas.fieldEquivPSL 3 s
    let σ : Mc →* MulAut Matrix.PSL3Four.PSL := (MulAut.congr d).toMonoidHom.comp ρ
    have hinner' : MulAut.innerSubgroup Matrix.PSL3Four.PSL ≤ σ.range := by
      rw [←MulAut.map_innerSubgroup_congr d]
      rintro _ ⟨a,ha,rfl⟩
      obtain ⟨x,rfl⟩ := hinner ha
      exact ⟨x,rfl⟩
    have hswap' : ∃ t : Mc, (t : G) ∈ (T : Subgroup G) ∧
        Matrix.PSL3.LinearThree.OuterExtensions.diagramAction Matrix.PSL3Four.F
          (n := 2) (by decide) (by simpa using Matrix.PSL3Four.card_F) (σ t) ≠ 1 := by
      obtain ⟨t,ht,hswap⟩ := hswap
      refine ⟨t,ht,?_⟩
      exact (Matrix.PSL3.LinearThree.FieldTransport.diagramAction_ne_one_congr_iff
        (by decide : 0 < 2) hF (by simpa using Matrix.PSL3Four.card_F) s (ρ t)).mpr hswap
    have hcomap : (MulAut.innerSubgroup Matrix.PSL3Four.PSL).comap σ =
        (MulAut.innerSubgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)).comap ρ := by
      ext x
      change MulAut.congr d (ρ x) ∈ MulAut.innerSubgroup Matrix.PSL3Four.PSL ↔ _
      rw [←MulAut.map_innerSubgroup_congr d,mem_map_equiv]
      simp only [MulEquiv.symm_apply_apply,Subgroup.mem_comap]
    have hplace' : (T : Subgroup G) ⊓
        ((MulAut.innerSubgroup Matrix.PSL3Four.PSL).comap σ).map Mc.subtype ≤ S := by
      rw [hcomap]
      exact hplace
    exact ExceptionalDiagram.source_exceptional_twoCore_le_of_marked_action
      hG T hempty hM hu hmany hcard e H hH K hK inferInstance hgen hm
      σ hinner' hswap' L hplace'

end CFSG.Quasithin.Chapter14.Section02
