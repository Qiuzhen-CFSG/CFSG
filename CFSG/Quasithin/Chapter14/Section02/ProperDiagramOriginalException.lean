module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramCubicCover
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramOriginalMcActor

/-!
# The actual exceptional quotient in the original diagram branch

Failure of the original maximal two-core to lie in the selected normalizer
forces field order four. Its actor fixes the quotient center pointwise,
so the cubic-cover calculation identifies the component quotient itself
with PSL₃(4). All quotient maps and the selected residual are retained.

Source: Aschbacher--Smith 14.2.12(1), printed p.984.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
 theorem source_linear_diagram_exception_of_core_not_normalized
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
    (hfail : ¬ M.pCoreIn 2 ≤ (T : Subgroup G) ⊓ normalizer
      ((markedParabolicResidual ((H ⊓ M).subgroupOf H) K mark
        (Matrix.PSL3.LinearThree.pointParabolic F)).map H.subtype : Set G)) :
    f = 2 ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 := by
  have hf2 : f = 2 := (ambient_linear_core_normalizes_or_four T M H
    hM.1.2 hH.1.1.2 K mark hmark hF hf).resolve_left hfail
  have hF4 : Nat.card F = 4 := by simpa [hf2] using hF
  let TH := T.subtype hH.1.1.2
  obtain ⟨_,hP,hN,_,_,_⟩ :=
    source_lemma_14_2_2_8_minimal hG T hempty hM hu hmany hcard e H hH
  have hmax : (H ⊓ M).subgroupOf H = ChapterB.minimalParabolicMax TH hP :=
    ChapterB.minimalParabolicMax_unique TH hP hN (fun x hx => ⟨x.property,hM.1.2 hx⟩)
  have hs : ¬Group.IsSolvable H := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt hn) generationParameter_le_one_of_solvable
  have hfailN : ¬ ((H ⊓ M).subgroupOf H).pCoreIn 2 ≤ normalizer
      (markedParabolicResidual ((H ⊓ M).subgroupOf H) K mark
        (Matrix.PSL3.LinearThree.pointParabolic F) : Set H) := by
    intro hnorm
    apply hfail
    obtain ⟨hQT,hQ⟩ := shared_sylow_twoCore_le_overlap_core T M H hM.1.2 hH.1.1.2
    exact le_inf hQT (hQ.trans ((map_mono hnorm).trans
      ((markedParabolicResidual ((H ⊓ M).subgroupOf H) K mark
        (Matrix.PSL3.LinearThree.pointParabolic F)).le_normalizer_map H.subtype)))
  have hc := original_linear_cover_equiv_of_core_not_normalized
    TH hP hs K hK hqK hgen hF4
  rw [←hmax] at hc
  exact ⟨hf2,F,inferInstance,inferInstance,hF4,hc mark hmark hfailN⟩

end CFSG.Quasithin.Chapter14.Section02
