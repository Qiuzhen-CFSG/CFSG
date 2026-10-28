module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramMcActor
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramAmbientCoreSelection
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramActorLift

/-!
# The actual Mc action in the original linear diagram branch

The full original source prefix gives the H-to-Mc containment and the
minimal-parabolic identification. The characteristic marked kernel then
constructs the Mc action. The original diagram witness lifts to a member
of the ambient Sylow subgroup, and inner actors lie in the normalizer of
the literal selected residual. Component normality in Mc remains the
preceding 14.2.9 placement input, rather than an action certificate.

Source: Aschbacher--Smith 14.2.9 and 14.2.12--13, printed pp.983--984.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

 theorem source_linear_diagram_Mc_action
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
    {F : Type*} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = 2^f) (hf : 1 < f)
    (mark : sourceImage ((H ⊓ M).subgroupOf H) K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (hmark : (componentOverlap ((H ⊓ M).subgroupOf H) K).map mark.toMonoidHom =
      Matrix.PSL3.LinearThree.borel F)
    (hmove : MovesDiagram ((H ⊓ M).subgroupOf H) K
      (T.subtype hH.1.1.2 : Subgroup H) mark
      (Matrix.PSL3.LinearThree.pointParabolic F) (Matrix.PSL3.LinearThree.lineParabolic F))
    (hMc : ((K.map H.subtype).subgroupOf Mc).Normal) :
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
  have hHMc : H ≤ Mc :=
    ((source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2).trans
      (InitialSource.centralizer_le_partner T hu)
  have hKMc : K.map H.subtype ≤ Mc := (map_subtype_le K).trans hHMc
  let TH := T.subtype hH.1.1.2
  obtain ⟨_,hP,hN,_,_,_⟩ :=
    source_lemma_14_2_2_8_minimal hG T hempty hM hu hmany hcard e H hH
  have hmax : (H ⊓ M).subgroupOf H = ChapterB.minimalParabolicMax TH hP :=
    ChapterB.minimalParabolicMax_unique TH hP hN (fun x hx => ⟨x.property,hM.1.2 hx⟩)
  have hs : ¬Group.IsSolvable H := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt hn) generationParameter_le_one_of_solvable
  have hk : ∀ mark : sourceImage ((H ⊓ M).subgroupOf H) K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) F,
      (markedParabolicMap ((H ⊓ M).subgroupOf H) K mark).ker.Characteristic := by
    rw [hmax]
    intro mark
    exact original_markedParabolicMap_kernel_characteristic TH hP hs K hK hqK hgen mark
  let := hk mark
  let := hMc
  let ρ := markedOvergroupActor H Mc ((H ⊓ M).subgroupOf H) K mark hKMc
  refine ⟨ρ,markedOvergroupActor_inner_range H Mc _ K mark hKMc,?_,?_⟩
  · obtain ⟨a,ha,hswap⟩ := hmove
    obtain ⟨t,ht,hat⟩ := sourceAutomizer_eq_markedParabolicActor_image
      ((H ⊓ M).subgroupOf H) K (TH : Subgroup H) mark a ha
    let tc : Mc := ⟨t,hHMc t.property⟩
    refine ⟨tc,ht,?_⟩
    intro hdiag
    apply hswap
    have heq : ρ tc = MulAut.congr mark a :=
      (markedOvergroupActor_restrict H Mc _ K mark hKMc t (hHMc t.property)).trans hat.symm
    have hp := Matrix.PSL3.LinearThree.OuterExtensions.diagramAction_spec
      F (by omega : 0 < f) hF (ρ tc) true
    have hl := Matrix.PSL3.LinearThree.OuterExtensions.diagramAction_spec
      F (by omega : 0 < f) hF (ρ tc) false
    rw [hdiag,Equiv.Perm.one_apply,heq] at hp hl
    exact ⟨hp,hl⟩
  · exact markedOvergroupActor_inner_preimage_normalizes H Mc (T : Subgroup G)
      ((H ⊓ M).subgroupOf H) K mark hmark hF hf hKMc hH.1.1.2 (by
        rw [map_subgroupOf_eq_of_le inf_le_left]
        exact le_inf hH.1.1.2 hM.1.2)

end CFSG.Quasithin.Chapter14.Section02
