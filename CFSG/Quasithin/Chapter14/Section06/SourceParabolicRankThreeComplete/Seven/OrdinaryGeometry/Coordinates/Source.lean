module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingSevenCoordinates
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.OrdinaryGeometry.Source

/-!
# The ordinary A₇ chart on the original generated parabolic

The literal component C = O²(I₀) is normal in I₀. Whole-module block coordinates
extend to its automorphisms, and transport through C.subtype gives coordinates
on the entire ambient image of U(C). Restriction to I₀ retains literal
conjugation and has exactly A₇ as the component image.

This discharges ChartInput for the unchanged H, d and I. The final application
removes the chart premise from the ordinary geometry consumer; recognition of
the original parabolic pair remains its separate input.
Source: Aschbacher--Smith, original14.6.10(5), printed pp.1029--1030.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryPermutation.SevenParabolic.Ordinary
variable {G : Type*} [Group G]

private theorem chart_of_normalizes (J C : Subgroup G)
    (hCJ : C ≤ J) (hJC : J ≤ normalizer (C : Set G))
    (hb : ChapterC.IsAlternatingBlock C 7) :
    Nonempty (Chart J C ((ChapterC.blockU C).map C.subtype)) := by
  obtain ⟨q, E0, f0, hf0, hE0⟩ := hb.seven_automorphism_coordinates
  let W := (ChapterC.blockU C).map C.subtype
  let j : ChapterC.blockU C ≃* W :=
    (ChapterC.blockU C).equivMapOfInjective C.subtype C.subtype_injective
  let E : W ≃* Multiplicative (core (Fin 7)) := j.symm.trans E0
  let f : J →* Equiv.Perm (Fin 7) :=
    f0.comp (C.normalizerMonoidHom.comp (inclusion hJC))
  have hn : J ≤ normalizer (W : Set G) := hJC.trans
    (normalizer_le_normalizer_characteristic_image C (ChapterC.blockU C))
  have hf (c : C) : f ⟨c.val, hCJ c.property⟩ =
      (q (QuotientGroup.mk' (pCore 2 C) c)).val := by
    have he : C.normalizerMonoidHom ⟨c.val, hJC (hCJ c.property)⟩ = MulAut.conj c := by
      ext x
      rfl
    change f0 (C.normalizerMonoidHom ⟨c.val, hJC (hCJ c.property)⟩) = _
    rw [he, hf0]
  refine ⟨{ moduleEquiv := E
            actor := f
            normalized := hn
            equivariant := ?_
            component_image := ?_ }⟩
  · intro a w
    have he : j.symm ⟨a.val * w.val * a.val⁻¹,
        le_normalizer_iff.mp hn a a.property w w.property⟩ =
        MulAut.characteristic (ChapterC.blockU C)
          (C.normalizerMonoidHom ⟨a.val, hJC a.property⟩) (j.symm w) := by
      apply j.injective
      rw [j.apply_symm_apply]
      apply Subtype.ext
      change a.val * w.val * a.val⁻¹ =
        a.val * (((j.symm w : ChapterC.blockU C) : C) : G) * a.val⁻¹
      congr 2
      exact (congrArg Subtype.val (j.apply_symm_apply w)).symm
    change (E0 (j.symm _)).toAdd =
      coreRepresentation (Fin 7) (f0 _) (E0 (j.symm w)).toAdd
    rw [he]
    exact hE0 _ _
  · apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      have hh := hf ⟨a.val, ha⟩
      simpa only [hh] using (q (QuotientGroup.mk' (pCore 2 C) ⟨a.val, ha⟩)).property
    · intro g hg
      obtain ⟨c, hc⟩ := q.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 C)) ⟨g,hg⟩
      exact ⟨⟨c.val, hCJ c.property⟩, c.property, (hf c).trans (congrArg Subtype.val hc)⟩

variable [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- Construct the exact whole-module chart for every original generated choice
in the ordinary A₇ branch. No faithful ambient action is assumed. -/
theorem source_chartInput : ChartInput hG T hempty hM hunique hmany hcard e hab := by
  intro H hH d I hI hb
  let J := sourceGeneratedParabolic T M Mc I d.H2
  let C := sourceGeneratedComponent T M Mc I d.H2
  have hCJ : C ≤ J := map_subtype_le _
  have hJC : J ≤ normalizer (C : Set G) := J.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image J (pResidual 2 J))
  exact chart_of_normalizes J C hCJ hJC hb

/-- Apply the chart to the original geometry consumer; only its independent
parabolic-pair recognition premise remains. -/
theorem ordinaryGeometryInput_of_pair
    (hp : PairInput hG T hempty hM hunique hmany hcard e hab) :
    OrdinaryGeometryInput hG T hempty hM hunique hmany hcard e hab :=
  ordinaryGeometryInput_of_chart_and_pair hG T hempty hM hunique hmany hcard e hab
    (source_chartInput hG T hempty hM hunique hmany hcard e hab) hp
end CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry
