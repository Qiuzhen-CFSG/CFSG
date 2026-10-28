module
public import CFSG.Quasithin.Chapter14.Section02.NormalKOne
public import Theory.SpecificGroups.PSU3.UniversalCover.BinaryModels

/-!
# The retained original unitary Bender quotient

The marked unitary row is initially a model of K's image in H/J.
Apply the complete scalar-cover theorem to the literal perfect central
cover from K/O₂(K). Its original quotient is PSU₃ or SU₃ over the same
field parameter, so it satisfies the genuine F.1.1 rank-one condition.
Normality and perfectness identify this same K with O²(H), and its
Sylow normalizer is T. This does not assert an exclusion of the unitary
row, nor discard its possible central subgroup of order three.

Source: Aschbacher--Smith E.2.2(2a), F.1.1(c), and the normal branch
of the construction preceding 14.2.9, printed pp.215--216, 259, 983.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H : Type*} [Group H] [Finite H]

theorem original_unitary_quotient_models
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {f : ℕ}
    (hm : UnitaryModel (ChapterB.minimalParabolicMax T hP) K f) :
    2 ≤ f ∧ (ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 (2^f) ∨
      ChapterF.Source.IsSU (K ⧸ pCore 2 K) 3 (2^f)) := by
  obtain ⟨F,hF,hfin,hchar,J,_hJ,hf,hcard,hconj,_hfix,d,_hB⟩ := hm
  let c := originalComponentStarCover T hP hs K hK hqK hgen
  let a := d.toMonoidHom.comp c.toMonoidHom
  have ha : Function.Surjective a := d.surjective.comp c.surjective
  let := hqK
  obtain ⟨ep⟩ | ⟨es⟩ :=
    BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.binary_cover_models J hf hcard hconj
      a ha (pCore_quotient_pCore_eq_bot 2)
  · exact ⟨hf,Or.inl ⟨F,hF,hfin,J,hcard,hconj,ep⟩⟩
  · exact ⟨hf,Or.inr ⟨F,hF,hfin,J,hcard,hconj,es⟩⟩

/-- Every original normal Bender row supplies the literal rank-one quotient for F.1.1. -/
theorem source_normal_bender_kOne
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {f : ℕ}
    (hm : BenderModel (ChapterB.minimalParabolicMax T hP) K f) :
    pResidual 2 H = K ∧
      (T : Subgroup H) ⊓ normalizer (K : Set H) = (T : Subgroup H) ∧
      (K.subgroupOf (K ⊔ (T : Subgroup H))).IsCComponent ∧
      ChapterF.Source.IsRankOneModel (K ⧸ pCore 2 K) := by
  have hr : pResidual 2 H = K := by
    let := hK.perfect
    apply le_antisymm
    · exact sInf_le ⟨inferInstance,
        isPGroup_quotient_of_sup_eq_top K (T : Subgroup H) T.isPGroup' hgen⟩
    · let : Group.IsNilpotent (H ⧸ pResidual 2 H) := (isPGroup_quotient_pResidual 2).isNilpotent
      exact le_of_isPerfect_of_solvable_quotient K (pResidual 2 H)
  refine ⟨hr,by rw [normalizer_eq_top,inf_top_eq],hK.subgroupOf le_sup_left,?_⟩
  rcases hm with hm | hm
  · obtain ⟨_,_,_,_,hq⟩ := source_normal_rank_one_kOne T hP hs K hK hqK hgen hm
    rcases hq with ⟨hf,hq⟩ | ⟨m,_,_,hq⟩
    · exact .linear f (by omega) hq
    · exact .suzuki m hq
  · obtain ⟨hf,hp | hs⟩ := original_unitary_quotient_models T hP hs K hK hqK hgen hm
    · exact .projective_unitary f (by omega) hp
    · exact .special_unitary f (by omega) hs
end CFSG.Quasithin.Chapter14.Section02
