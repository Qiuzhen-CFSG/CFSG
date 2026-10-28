module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Estimates.Cover
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.AlternatingOffenders
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.Representation.NormalElementaryQuotient.FixedIndex

/-!
# Offenders on the original moved cover

A maximum elementary subgroup of the original characteristic radical is
an offender on the entire moved cover. The actual surjective quotient
transfers its inequality to the natural four-space. In the A₆ image case,
the unique even offender has order four; both fixed codimensions are two.
Consequently the whole elementary Thompson image is the same four-group.
The final application gives index four for the literal subgroup centralizer.

These are local estimates used in the first paragraph of MS93 (3.8),
printed p.877. They retain both moved orders and the original radical;
the critical-pair commutator bounds remain separate local work.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Cover
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)

local notation "p" => SectionFive.coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d)
local notation "q" => MonoidHom.rangeRestrict (projection h e hz hn d)

/-- A maximum elementary subgroup acts as an offender on the whole cover. -/
theorem maxElementary_cover_offender (E : Subgroup d.overgroup)
    (hE : E ∈ Stellmacher.elementaryAbelianMaxSubgroups d.radical)
    (hne : ¬ E ≤ pCore 2 d.overgroup) :
    IsOffender (action h e hz hn d) (E.map q) := by
  let := replacementMoved_normal h d
  apply NormalElementaryQuotient.maxElementary_isOffender
    (replacementMoved d) q (projection h e hz hn d).rangeRestrict_surjective
    ((MonoidHom.ker_rangeRestrict _).trans
      ((projection_kernel h e hz hn d).trans (moved_centralizer h e hz hn d).symm))
    d.radical E
  · intro v hv
    exact replacement_core_le_radical h d
      ((mem_omegaCenterIn_iff _ _).mp (replacementMoved_le_omegaCenter h d hv)).1
  · exact hE
  · simpa only [MonoidHom.ker_rangeRestrict, projection_kernel] using hne

/-- The same actual subgroup is an offender on the natural central quotient. -/
theorem maxElementary_natural_offender (E : Subgroup d.overgroup)
    (hE : E ∈ Stellmacher.elementaryAbelianMaxSubgroups d.radical)
    (hne : ¬ E ≤ pCore 2 d.overgroup) :
    IsOffender (BinaryPermutation.naturalRepresentation (Fin 6))
      (E.map (projection h e hz hn d)) := by
  let σ := (BinaryPermutation.naturalRepresentation (Fin 6)).comp
    (projection h e hz hn d).range.subtype
  have ho := maxElementary_cover_offender h e hz hn d E hE hne
  have hq : IsOffender σ (E.map q) := ⟨ho.1,
    (fixedCodim_le_of_equivariant_surjection (action h e hz hn d) σ p
      (SectionFive.coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (map_equivariant h e hz hn d) (E.map q)).trans ho.2⟩
  have ht := hq.map_equivariant σ (BinaryPermutation.naturalRepresentation (Fin 6))
    (projection h e hz hn d).range.subtype
    (projection h e hz hn d).range.subtype_injective (LinearEquiv.refl _ _)
    (fun _ _ => rfl)
  rw [Subgroup.map_map] at ht
  exact ht

/-- Source (3.8)'s unique even offender occurs for the literal characteristic
radical, with no natural subgroup or split-cover assumption. -/
theorem maxElementary_even_image
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6))
    (E : Subgroup d.overgroup)
    (hE : E ∈ Stellmacher.elementaryAbelianMaxSubgroups d.radical)
    (hne : ¬ E ≤ pCore 2 d.overgroup) :
    ChapterB.Offenders.IsConjugateTo (E.map (projection h e hz hn d))
        (ChapterB.Offenders.evenPart 6) ∧
      Nat.card (E.map (projection h e hz hn d)) = 4 ∧
      fixedCodim (BinaryPermutation.naturalRepresentation (Fin 6))
        (E.map (projection h e hz hn d)) = 2 := by
  have he : E.map (projection h e hz hn d) ≤ alternatingGroup (Fin 6) := by
    rw [← himage]
    exact map_le_range _ _
  have ho := maxElementary_natural_offender h e hz hn d E hE hne
  exact ⟨(ChapterC.NaturalSixControl.AlternatingOffenders.even_offender_iff _ he).mp ho,
    ChapterC.NaturalSixControl.AlternatingOffenders.even_offender_card he ho,
    ChapterC.NaturalSixControl.AlternatingOffenders.even_offender_codim he ho⟩

/-- MS3 supplies a maximum elementary offender on the actual nonsplit cover. -/
theorem exists_maxElementary_offender :
    ∃ E ∈ Stellmacher.elementaryAbelianMaxSubgroups d.radical,
      ¬ E ≤ pCore 2 d.overgroup ∧
      IsOffender (BinaryPermutation.naturalRepresentation (Fin 6))
        (E.map (projection h e hz hn d)) := by
  have hnot := (replacement_characteristic h d).thompson_not_le_core
    (replacement_radical_isPGroup h d) (replacement_radical_ne_bot h d)
    (replacement_core_le_radical h d)
  have hex : ∃ E ∈ Stellmacher.elementaryAbelianMaxSubgroups d.radical,
      ¬ E ≤ pCore 2 d.overgroup := by
    by_contra! hall
    exact hnot (sSup_le hall)
  obtain ⟨E, hE, hne⟩ := hex
  exact ⟨E, hE, hne, maxElementary_natural_offender h e hz hn d E hE hne⟩

/-- Every maximum elementary offender has the same image in the derived case. -/
theorem maxElementary_image_unique
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6))
    (E F : Subgroup d.overgroup)
    (hE : E ∈ Stellmacher.elementaryAbelianMaxSubgroups d.radical)
    (hF : F ∈ Stellmacher.elementaryAbelianMaxSubgroups d.radical)
    (hneE : ¬ E ≤ pCore 2 d.overgroup) (hneF : ¬ F ≤ pCore 2 d.overgroup) :
    E.map (projection h e hz hn d) = F.map (projection h e hz hn d) := by
  apply ChapterC.NaturalSixControl.AlternatingOffenders.even_offender_unique
    ((replacement_radical_isPGroup h d).map (projection h e hz hn d))
    (show d.radical.map (projection h e hz hn d) ≤ alternatingGroup (Fin 6) by
      rw [← himage]; exact map_le_range _ _)
    (map_mono hE.1) (map_mono hF.1)
  · exact maxElementary_natural_offender h e hz hn d E hE hneE
  · exact maxElementary_natural_offender h e hz hn d F hF hneF

/-- The elementary Thompson subgroup has precisely the unique offender image. -/
theorem thompson_image_eq
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6))
    (E : Subgroup d.overgroup)
    (hE : E ∈ Stellmacher.elementaryAbelianMaxSubgroups d.radical)
    (hne : ¬ E ≤ pCore 2 d.overgroup) :
    (Stellmacher.elementaryAbelianMaxJ d.radical).map (projection h e hz hn d) =
      E.map (projection h e hz hn d) := by
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro F hF
    apply map_le_iff_le_comap.mp
    by_cases hFQ : F ≤ pCore 2 d.overgroup
    · have hzF : F.map (projection h e hz hn d) = ⊥ := by
        apply F.map_eq_bot_iff.mpr
        rwa [projection_kernel]
      rw [hzF]
      exact bot_le
    · rw [maxElementary_image_unique h e hz hn d himage F E hF hE hFQ hne]
  · exact map_mono (le_sSup hE)

/-- Source (3.8)'s order-four offender controls the whole elementary Thompson image. -/
theorem thompson_even_image
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6)) :
    ChapterB.Offenders.IsConjugateTo
        ((Stellmacher.elementaryAbelianMaxJ d.radical).map (projection h e hz hn d))
        (ChapterB.Offenders.evenPart 6) ∧
      Nat.card ((Stellmacher.elementaryAbelianMaxJ d.radical).map
        (projection h e hz hn d)) = 4 := by
  obtain ⟨E, hE, hne, _⟩ := exists_maxElementary_offender h e hz hn d
  rw [thompson_image_eq h e hz hn d himage E hE hne]
  exact ⟨(maxElementary_even_image h e hz hn d himage E hE hne).1,
    (maxElementary_even_image h e hz hn d himage E hE hne).2.1⟩

/-- The offender index on the entire central cover is exactly four, including
the augmentation-cover case. -/
theorem maxElementary_cover_codim
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6))
    (E : Subgroup d.overgroup)
    (hE : E ∈ Stellmacher.elementaryAbelianMaxSubgroups d.radical)
    (hne : ¬ E ≤ pCore 2 d.overgroup) :
    fixedCodim (action h e hz hn d) (E.map q) = 2 := by
  let σ := (BinaryPermutation.naturalRepresentation (Fin 6)).comp
    (projection h e hz hn d).range.subtype
  have hm := maxElementary_even_image h e hz hn d himage E hE hne
  have heq : (E.map q).map (projection h e hz hn d).range.subtype =
      E.map (projection h e hz hn d) := by
    rw [map_map]
    rfl
  have hr : rank (E.map q) = 2 := by
    rw [← rank_map_injective (projection h e hz hn d).range.subtype
      (projection h e hz hn d).range.subtype_injective, heq]
    change Nat.log 2 (Nat.card (E.map (projection h e hz hn d))) = 2
    rw [hm.2.1]
    decide
  have hq : fixedCodim σ (E.map q) = 2 := by
    unfold fixedCodim σ
    rw [fixedSpace_comp_map, heq]
    exact hm.2.2
  have hlo := fixedCodim_le_of_equivariant_surjection (action h e hz hn d) σ p
    (SectionFive.coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
    (map_equivariant h e hz hn d) (E.map q)
  have hup := (maxElementary_cover_offender h e hz hn d E hE hne).2
  omega

/-- Literal subgroup-index application of the cover offender estimate. -/
theorem maxElementary_centralizer_index
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6))
    (E : Subgroup d.overgroup)
    (hE : E ∈ Stellmacher.elementaryAbelianMaxSubgroups d.radical)
    (hne : ¬ E ≤ pCore 2 d.overgroup) :
    (centralizer (E : Set d.overgroup)).relIndex (replacementMoved d) = 4 := by
  let := replacementMoved_normal h d
  have he : (centralizer (E : Set d.overgroup)).relIndex (replacementMoved d) =
      2 ^ fixedCodim (action h e hz hn d) (E.map q) :=
    NormalElementaryQuotient.centralizer_index_eq_fixedCodim _ _ _ _ E
  rw [he, maxElementary_cover_codim h e hz hn d himage E hE hne]
  norm_num

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Cover
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
