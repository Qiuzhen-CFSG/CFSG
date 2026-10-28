module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortContainment
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSpecialFieldAction
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Inner

/-!
# Outer parity and full centralizers at odd ordinary unitary degree

The exact inner preimage of the whole middle identifies the outer index of
any one marked U₄ extension with the reduced Borel index in the original
common normalizer. For the ordinary comparison the right PSL₂(2^m) quotient
gives |T:sourceS| dividing m. At odd m, this two-power index is one. The
reduced Borel consequently contains the original ambient Sylow and has odd
index in the whole middle. This discharges the same extension's parity
premise and applies the full F.4.42 ambient centralizer theorem.

The specialized conclusion covers both ordinary orientations. The original
ordinary even-degree and degree-two rows, including q=4, remain in the
unconditional source problem; the generic index identity retains them.
No ambient order inequality is assumed or proved here.

Source: Aschbacher--Smith F.4.29(2),38,42 and 5.3.3, printed
pp.289,294--296,659 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour ChapterF.SourceCompletion.UnitaryNonbinary
open UnitaryCompletion
variable {G : Type*} [Group G]

/-- The same extension's full outer index is the reduced whole-overlap index
in the original common normalizer, for either marked orientation. -/
theorem UnitaryFourNormalizerMarking.outer_index_eq_source
    {L K S : Subgroup G} {m : ℕ} {hm : 1 ≤ m}
    (r : UnitaryFourNormalizerMarking L K S m hm) :
    (inner (ProjectiveGroup m hm)).relIndex r.extension.carrier =
      (ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1).relIndex
        (normalizer (L : Set G) ⊓ normalizer (K : Set G)) := by
  have hr : r.extension.baseHom.range = (inner (ProjectiveGroup m hm)).subgroupOf r.extension.carrier := by
    ext x
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨b,rfl⟩
    · rintro ⟨b,hb⟩
      exact ⟨b,Subtype.ext hb⟩
  have hn : (inner (ProjectiveGroup m hm)).relIndex r.extension.carrier =
      r.extension.nativeOverlap.index := by
    rw [r.extension.nativeOverlap_index_eq,hr]
    rfl
  rw [hn]
  rcases r.marking with ⟨a,f,F,_,_,hD,_⟩ | ⟨a,f,F,_,_,hD,_⟩
  · have he : r.extension.nativeOverlap.comap F.middle.toMonoidHom =
        (ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1).subgroupOf
          (normalizer (L : Set G) ⊓ normalizer (K : Set G)) := by
      ext x
      change (F.middle x).val ∈ inner (ProjectiveGroup m hm) ↔ _
      rw [hD]
      exact UnitaryFullNormalizer.four_inner_preimage f x
    rw [←r.extension.nativeOverlap.index_comap_of_surjective
      (f := F.middle.toMonoidHom) F.middle.surjective,he]
    rfl
  · have he : r.extension.nativeOverlap.comap F.middle.toMonoidHom =
        (ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1).subgroupOf
          (normalizer (L : Set G) ⊓ normalizer (K : Set G)) := by
      ext x
      change (F.middle x).val ∈ inner (ProjectiveGroup m hm) ↔ _
      rw [hD]
      exact UnitaryFullNormalizer.four_inner_preimage_reverse f x
    rw [←r.extension.nativeOverlap.index_comap_of_surjective
      (f := F.middle.toMonoidHom) F.middle.surjective,he]
    rfl

variable [Finite G] {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse))
include d h hH hp hm hc

/-- The ordinary row's right PSL₂ field has degree m, so |T:sourceS| divides m. -/
theorem Preparation.unitaryFour_ordinary_sylow_index_dvd :
    (sourceS L H).relIndex (T : Subgroup G) ∣ m := by
  have hs := d.unitary_ordinary_sourceS_eq h hH.1.1.2 hp m hm hc
  have he := d.common_sylow_of_comparison h hH.1.1.2 hp (.unitary m hm hc)
  have hS (i : Fin 2) : sourceS L H ≤ ![L,residual H] i := by
    rw [hs]
    fin_cases i
    · exact inf_le_right
    · exact he ▸ inf_le_right
  exact d.residual_sylow_index_dvd h hH.1.1.2 hS
    (d.unitary_local_structure h hH.1.1.2 hp m hm hc).2.2.2.2

/-- At odd unitary degree the ordinary source Sylow is the full ambient Sylow. -/
theorem Preparation.unitaryFour_ordinary_sourceS_eq_sylow_of_odd (hmOdd : Odd m) :
    sourceS L H = (T : Subgroup G) := by
  have hd := d.unitaryFour_ordinary_sylow_index_dvd h hH hp m hm hc
  obtain ⟨k,hk⟩ := T.isPGroup'.exists_card_eq
  have ht : (sourceS L H).relIndex (T : Subgroup G) ∣ 2^k := by
    rw [←hk]
    exact relIndex_dvd_card _ _
  exact le_antisymm (sourceS_le_sylow h.sylow_normalizes hH.1.1.2)
    (relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes (hmOdd.coprime_two_right.pow_right k) hd ht))

/-- Odd ordinary degree discharges the parity premise on the same marked extension. -/
theorem Preparation.unitaryFour_ordinary_outer_odd_of_odd (hmOdd : Odd m)
    (r : UnitaryFourNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) m hm) :
    ¬ 2 ∣ (inner (ProjectiveGroup m hm)).relIndex r.extension.carrier := by
  let B := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0 ⊓
    ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 1
  let D := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  have hTL : (T : Subgroup G) ⊓ L = T :=
    (d.unitary_ordinary_sourceS_eq h hH.1.1.2 hp m hm hc).symm.trans
      (d.unitaryFour_ordinary_sourceS_eq_sylow_of_odd h hH hp m hm hc hmOdd)
  have hTB : (T : Subgroup G) ≤ B := by
    rw [←hTL]
    exact le_inf (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_left)
  have hBD : B ≤ D := le_inf (inf_le_left.trans r.left_le) (inf_le_right.trans r.right_le)
  rw [r.outer_index_eq_source]
  intro hbad
  exact (T.subtype (hTB.trans hBD)).not_dvd_index
    (hbad.trans (index_dvd_of_le (show (T.subtype (hTB.trans hBD) : Subgroup D) ≤ B.subgroupOf D from
      fun x hx => hTB hx)))

/-- Both full ambient root-centralizer comparisons now have no parity premise
in the ordinary odd-degree branch, on any one fixed marked extension. -/
theorem Preparation.unitaryFour_ordinary_ambient_centralizers_of_odd (hmOdd : Odd m)
    (r : UnitaryFourNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) m hm) :
    ∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) (amalgam m hm).reverse,
      ∃ f : UnitaryNativeLift.Four.LiftReverse m hm a,
      ∃ F : RankTwoAmalgam.Iso (normalizerDiagram L (residual H)) r.extension.amalgam.reverse,
        (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
        (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
        (∀ z, (F.middle z).val = (f.action z).val) ∧
        UnitarySource.FourLongCentralizerComparison r F ∧
        UnitarySource.FourAmbientShortCentralizerComparison r a F :=
  d.unitaryFour_ambient_centralizers_of_odd_outer h hH hp m hm (Or.inl hc) r
    (d.unitaryFour_ordinary_outer_odd_of_odd h hH hp m hm hc hmOdd r)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
