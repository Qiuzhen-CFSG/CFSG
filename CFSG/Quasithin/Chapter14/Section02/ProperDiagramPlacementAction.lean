module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramPlacement
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramOriginalMcActor

/-!
# Diagram placement feeds the original Mc action

Equality of the selected and containing component images in Mc/O₂(Mc)
proves the original component placement, including normality in Mc. The
linear-diagram consumer then constructs the actual Mc action and retains
its nontrivial diagram actor in the original Sylow subgroup. The preceding
marked embedding screen remains the explicit image-equality premise.

Source: Aschbacher--Smith 14.2.9 and 14.2.12--13, printed pp.983--984.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

theorem source_linear_diagram_Mc_action_of_twoCore_images
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
    (himage : ∀ D : Subgroup G, D ∈ Chapter1.cComponentsIn Mc →
      K.map H.subtype ≤ D → (D.subgroupOf Mc).Normal →
      ((K.map H.subtype).subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc)) =
        (D.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) :
    ∃ ρ : Mc →* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F),
      MulAut.innerSubgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) ≤ ρ.range ∧
      (∃ t : Mc, (t : G) ∈ (T : Subgroup G) ∧
        Matrix.PSL3.LinearThree.OuterExtensions.diagramAction F
          (n := f) (by omega) hF (ρ t) ≠ 1) ∧
      (T : Subgroup G) ⊓
        ((MulAut.innerSubgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)).comap ρ).map Mc.subtype ≤
        (T : Subgroup G) ⊓ normalizer
          ((markedParabolicResidual ((H ⊓ M).subgroupOf H) K mark
            (Matrix.PSL3.LinearThree.pointParabolic F)).map H.subtype : Set G) := by
  have hm : DiagramModel ((H ⊓ M).subgroupOf H) K
      (T.subtype hH.1.1.2 : Subgroup H) f :=
    Or.inl ⟨F,inferInstance,inferInstance,inferInstance,by omega,hF,mark,hmark,hmove⟩
  have hplace := source_diagram_component_placement_of_twoCore_images
    hG T hempty hM hu hmany hcard e H hH hn K hK hqK hgen hf hm himage
  exact source_linear_diagram_Mc_action hG T hempty hM hu hmany hcard e H hH hn
    K hK hqK hgen hF hf mark hmark hmove hplace.2

end CFSG.Quasithin.Chapter14.Section02
