module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryNativeLift.Actions
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.SylowGeometry

/-!
# The full inner preimage of the native unitary-four flag action

The native overlap is a Sylow normalizer, hence self-normalizing. An inner
flag automorphism normalizes the overlap and therefore comes from it. Faithful
lifting and the exact whole-overlap marking then identify the full inner
preimage with the reduced source overlap, in both orientations.

Source: the faithful full-normalizer realization in Aschbacher–Smith 5.3.2,
printed p.659, and the extension convention of F.4.3, printed p.274.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryFullNormalizer
open ChapterF.GreenBook.LieModels.UnitaryFour
open ChapterF.SourceCompletion.UnitaryNonbinary

/-- The whole native overlap is self-normalizing. -/
theorem four_overlap_normalizer (m : ℕ) (hm : 1 ≤ m) :
    normalizer (overlap m hm : Set (ProjectiveGroup m hm)) = overlap m hm := by
  rw [← projectiveSylow_normalizer m hm]
  exact (projectiveSylow m hm).normalizer_normalizer

/-- Inner automorphisms preserving both endpoint types pointwise on the
flag come from the whole Borel. -/
theorem four_inner_flag (m : ℕ) (hm : 1 ≤ m) (b : ProjectiveGroup m hm)
    (hb : MulAut.conj b ∈ Chapter5.UnitaryNativeLift.Four.flagAutomorphisms m hm) :
    b ∈ overlap m hm := by
  have hP : b ∈ normalizer (pointParabolic m hm : Set (ProjectiveGroup m hm)) :=
    mem_normalizer_iff_map_conj_eq.mpr hb.1
  have hQ : b ∈ normalizer (planeParabolic m hm : Set (ProjectiveGroup m hm)) :=
    mem_normalizer_iff_map_conj_eq.mpr hb.2
  have hh := inf_normalizer_le_normalizer_inf ⟨hP,hQ⟩
  rw [exact_overlap m hm, four_overlap_normalizer m hm] at hh
  exact hh

variable {G : Type*} [Group G] {L K S : Subgroup G} {m : ℕ} {hm : 1 ≤ m}

/-- All inner automorphisms, rather than only Borel-inner marked actions,
have precisely the reduced overlap as their preimage. -/
theorem four_inner_preimage
    {a : UnitarySource.MarkedMiddleAction L K S (amalgam m hm)}
    (f : UnitaryNativeLift.Four.Lift m hm a)
    (g : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G)) :
    (f.action g).val ∈ inner (ProjectiveGroup m hm) ↔
      g.val ∈ ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1 := by
  constructor
  · rintro ⟨b,hb⟩
    have hbB := four_inner_flag m hm b (hb.symm ▸ (f.action g).property)
    let c := a.comparison.middle.symm ⟨b,hbB⟩
    have he : f.action (inclusion a.middle_le c) = f.action g := by
      apply Subtype.ext
      rw [UnitaryNativeLift.Four.inner_action f]
      change MulAut.conj (a.comparison.middle c).val = (f.action g).val
      simpa only [c, a.comparison.middle.apply_symm_apply] using hb
    exact (congrArg Subtype.val (f.faithful he)) ▸ c.property
  · intro hg
    refine ⟨(a.comparison.middle ⟨g.val,hg⟩).val, ?_⟩
    exact (congrArg Subtype.val
      (UnitaryNativeLift.Four.inner_action f ⟨g.val,hg⟩)).symm

/-- The same full inner preimage with the native endpoints interchanged. -/
theorem four_inner_preimage_reverse
    {a : UnitarySource.MarkedMiddleAction L K S (amalgam m hm).reverse}
    (f : UnitaryNativeLift.Four.LiftReverse m hm a)
    (g : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G)) :
    (f.action g).val ∈ inner (ProjectiveGroup m hm) ↔
      g.val ∈ ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1 := by
  constructor
  · rintro ⟨b,hb⟩
    have hbB := four_inner_flag m hm b (hb.symm ▸ (f.action g).property)
    let c := a.comparison.middle.symm ⟨b,hbB⟩
    have he : f.action (inclusion a.middle_le c) = f.action g := by
      apply Subtype.ext
      rw [UnitaryNativeLift.Four.inner_actionReverse f]
      change MulAut.conj (a.comparison.middle c).val = (f.action g).val
      simpa only [c, a.comparison.middle.apply_symm_apply] using hb
    exact (congrArg Subtype.val (f.faithful he)) ▸ c.property
  · intro hg
    refine ⟨(a.comparison.middle ⟨g.val,hg⟩).val, ?_⟩
    exact (congrArg Subtype.val
      (UnitaryNativeLift.Four.inner_actionReverse f ⟨g.val,hg⟩)).symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryFullNormalizer
