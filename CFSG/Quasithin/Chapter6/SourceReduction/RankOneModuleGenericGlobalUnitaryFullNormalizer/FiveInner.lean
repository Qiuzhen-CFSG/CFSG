module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryNativeLift.Actions
public import Theory.SpecificGroups.ClassicalUnitary.FullNormalizerRealization.FiveLine
public import Theory.GroupTheory.CharacteristicCentralizerSylow

/-!
# The full inner preimage for the projective unitary-five flag

An element normalizing the line parabolic preserves its solvable residual
and the characteristic two-core of that residual. This is the literal line
radical; its fixed-space calculation forces the element into the parabolic.
The whole overlap is a Sylow normalizer there and is self-normalizing there.
Consequently an inner automorphism preserving both parabolics comes from
the overlap. The exact native lift then identifies its full inner preimage
in the original common normalizer, in both orientations.

Source: Aschbacher–Smith 5.3.2 and F.4.3, printed pp.659 and274.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryFullNormalizer
open ChapterF.SourceCompletion.UnitaryNonbinary

/-- The actual projective line parabolic is self-normalizing. -/
theorem five_leftParabolic_normalizer (U : ChapterF.GreenBook.UnitaryFive.Model 4) :
    normalizer (U.leftParabolic : Set U.Carrier) = U.leftParabolic := by
  apply le_antisymm _ U.leftParabolic.le_normalizer
  let : U.leftLocal.Characteristic := by
    change (solvableResidual U.leftParabolic).Characteristic
    infer_instance
  have h₁ := normalizer_le_normalizer_characteristic_image U.leftParabolic U.leftLocal
  have h₂ := normalizer_le_normalizer_characteristic_map U.leftParabolic.subtype
    U.leftParabolic.subtype_injective U.leftLocal (pCore 2 U.leftLocal)
  rw [U.map_leftCore_subtype] at h₂
  exact (h₁.trans h₂).trans
    (Theory.SpecificGroups.UnitaryFive.FullNormalizerRealization.normalizer_line_radical_le_parabolic
      U.form U.conjugation U.card U.matrix)

/-- Inner automorphisms preserving the native line and plane parabolics
come from the entire overlap, including its odd-order elements. -/
theorem five_inner_flag (U : ChapterF.GreenBook.UnitaryFive.Model 4) (b : U.Carrier)
    (hb : MulAut.conj b ∈ Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U) :
    b ∈ U.overlap := by
  have hP : b ∈ normalizer (U.leftParabolic : Set U.Carrier) :=
    mem_normalizer_iff_map_conj_eq.mpr hb.1
  have hQ : b ∈ normalizer (U.rightParabolic : Set U.Carrier) :=
    mem_normalizer_iff_map_conj_eq.mpr hb.2
  have hB : b ∈ normalizer (U.overlap : Set U.Carrier) :=
    inf_normalizer_le_normalizer_inf ⟨hP,hQ⟩
  have hbP : b ∈ U.leftParabolic := five_leftParabolic_normalizer U ▸ hP
  have hn : (⟨b,hbP⟩ : U.leftParabolic) ∈
      normalizer (U.overlap.subgroupOf U.leftParabolic : Set U.leftParabolic) :=
    le_normalizer_comap U.leftParabolic.subtype hB
  rw [←U.leftParabolicSylow_normalizer,U.leftParabolicSylow.normalizer_normalizer,
    U.leftParabolicSylow_normalizer] at hn
  exact hn

variable {G : Type*} [Group G] {L K S : Subgroup G} {U : ChapterF.GreenBook.UnitaryFive.Model 4}

/-- All inner automorphisms, rather than only Borel-inner marked actions,
have precisely the reduced overlap as their preimage. -/
theorem five_inner_preimage
    {a : UnitarySource.MarkedMiddleAction L K S U.amalgam}
    (f : UnitaryNativeLift.Five.Lift U a)
    (g : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G)) :
    (f.action g).val ∈ inner U.Carrier ↔
      g.val ∈ ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1 := by
  constructor
  · rintro ⟨b,hb⟩
    have hbB := five_inner_flag U b (hb.symm ▸ (f.action g).property)
    let c := a.comparison.middle.symm ⟨b,hbB⟩
    have he : f.action (inclusion a.middle_le c) = f.action g := by
      apply Subtype.ext
      rw [UnitaryNativeLift.Five.inner_action f]
      change MulAut.conj (a.comparison.middle c).val = (f.action g).val
      simpa only [c, a.comparison.middle.apply_symm_apply] using hb
    exact (congrArg Subtype.val (f.faithful he)) ▸ c.property
  · intro hg
    refine ⟨(a.comparison.middle ⟨g.val,hg⟩).val, ?_⟩
    exact (congrArg Subtype.val
      (UnitaryNativeLift.Five.inner_action f ⟨g.val,hg⟩)).symm

/-- The same full inner preimage with the native endpoints interchanged. -/
theorem five_inner_preimage_reverse
    {a : UnitarySource.MarkedMiddleAction L K S U.amalgam.reverse}
    (f : UnitaryNativeLift.Five.LiftReverse U a)
    (g : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G)) :
    (f.action g).val ∈ inner U.Carrier ↔
      g.val ∈ ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1 := by
  constructor
  · rintro ⟨b,hb⟩
    have hbB := five_inner_flag U b (hb.symm ▸ (f.action g).property)
    let c := a.comparison.middle.symm ⟨b,hbB⟩
    have he : f.action (inclusion a.middle_le c) = f.action g := by
      apply Subtype.ext
      rw [UnitaryNativeLift.Five.inner_actionReverse f]
      change MulAut.conj (a.comparison.middle c).val = (f.action g).val
      simpa only [c, a.comparison.middle.apply_symm_apply] using hb
    exact (congrArg Subtype.val (f.faithful he)) ▸ c.property
  · intro hg
    refine ⟨(a.comparison.middle ⟨g.val,hg⟩).val, ?_⟩
    exact (congrArg Subtype.val
      (UnitaryNativeLift.Five.inner_actionReverse f ⟨g.val,hg⟩)).symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryFullNormalizer
