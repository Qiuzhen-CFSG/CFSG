module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoMarkedComparison
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoTensorApplication

/-!
# The literal Aut(J₂) comparison for the mixed tensor pair

The paired-action recognition and split-extension comparison identify the
original endpoints H and AT and the whole overlap BT with the concrete
Aut(J₂) parabolics. Both inclusion squares commute. The earlier compatible
reduced recognition remains explicit; no compatibility is inferred from the
weaker parabolic-model predicate.

Source: DGS (15.3), pp.228–231, applied to the original F.1.11–12 tensor pair.
-/

public section
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Subgroup Theory.GroupTheory Chapter3.Section02 MixedZeroCore
open ChapterF.Source ChapterF.Source.DGS85.OriginalExtension ChapterF.GreenBook
open SuzukiContainment
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- The actual whole BT and both original endpoint inclusions have the
Aut(J₂) comparison in the proper reduced-J₂ branch. -/
theorem mixed_cubic_factor_autJ2_iso_of_reduced_j2
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥)
    (e : RankTwoAmalgam.Iso
      (reducedAmalgam ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G))
      HallJanko.j2Model.toMarking.amalgam)
    (hne : (T : Subgroup G) ≠ reducedSylow
      ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)) :
    ∃ hBH : B ⊔ (T : Subgroup G) ≤ H,
      Nonempty (RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups H (B ⊔ (T : Subgroup G)) (A ⊔ (T : Subgroup G))
          hBH (sup_le_sup_right hBA _)) HallJanko.autJ2Model.toMarking.amalgam) := by
  obtain ⟨hf,_,_,_,hb,hp,hAT⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  obtain ⟨E,_,_,_⟩ := JankoTwo.SplitComparison.original_autJ2_iso hf 0 1 e hne
  have hBH : B ⊔ (T : Subgroup G) ≤ H := by
    have hh : commonBorel ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G) ≤
        parabolic ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G) 0 :=
      commonBorel_le_parabolic 0
    simpa only [hb,hp] using hh
  let f : RankTwoAmalgam.Iso
      (originalAmalgam ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G))
      (RankTwoAmalgam.ofSubgroups H (B ⊔ (T : Subgroup G)) (A ⊔ (T : Subgroup G))
        hBH (sup_le_sup_right hBA _)) := {
    left := MulEquiv.subgroupCongr hp
    middle := MulEquiv.subgroupCongr hb
    right := MulEquiv.subgroupCongr hAT
    left_commutes := fun _ => Subtype.ext rfl
    right_commutes := fun _ => Subtype.ext rfl }
  exact ⟨hBH,⟨f.symm.trans E⟩⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
