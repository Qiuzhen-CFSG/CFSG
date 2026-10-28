module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.OffenderImage
public import Theory.SpecificGroups.BinaryLinear.Parabolics

/-!
# The original Thompson image and its two-space parabolic

The same Sylow-compatible marking identifies A0 with the unipotent radical
at the coordinate plane. The normalizer of that radical in GL4(2) is its
plane stabilizer. Substitution of the proved original Thompson image gives
both identities on the literal quotient of the chosen doubled branch.

This supplies the B.4.9 geometry used in 12.1.4. It does not assume a
normalizer model or change the source point, original Sylow, or action map.
The remaining whole-module splitting and ambient Sylow contradiction belong
to qt-d-double-natural-pure-fusion, with final centralizer assembly retained
by qt-d-double-natural-centralizers.
Source: Aschbacher--Smith, 12.1.4, printed p.790; B.4.9(2iii), pp.92,94.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
open SourceFourActors
variable {M E : Type*} [Group M] [AddCommGroup E] [Module (ZMod 2) E]
  (S : SourceSetup 4 M E) (P : Sylow 2 M)

/-- The marked offender is the unipotent radical at the actual coordinate plane. -/
theorem four_A0_radical :
    ((A0 S P).subgroupOf (componentLayer M)).map (layerCoordinates S P).toMonoidHom =
      BinaryLinear.radical BinaryNaturalDual.FourActors.A0Plane := by
  have hcoord : BinaryNaturalDual.FourActors.A0 =
      BinaryNaturalDual.FourActors.radicalImage BinaryNaturalDual.FourActors.A0Plane :=
    BinaryNaturalDual.FourActors.A0_eq_radicalImage
      (BinaryNaturalDual.FourActors.PermutationCatalogue.actor_card 0)
  have he : (A0 S P).subgroupOf (componentLayer M) =
      (BinaryLinear.radical BinaryNaturalDual.FourActors.A0Plane).comap
        (layerCoordinates S P).toMonoidHom := by
    ext x
    change (group S P (x : M) ∈ BinaryNaturalDual.FourActors.A0) ↔ _
    rw [group_layer,hcoord]
    exact mem_map_iff_mem (MulAut.conj_injective_of_center_eq_bot
      BinaryNaturalDual.FourActors.center_linear_eq_bot)
  rw [he,map_comap_eq_self_of_surjective (layerCoordinates S P).surjective]

/-- The inner normalizer of this exact offender is the two-space parabolic. -/
theorem four_A0_inner_normalizer :
    (normalizer (((A0 S P).subgroupOf (componentLayer M)) : Set (componentLayer M))).map
      (layerCoordinates S P).toMonoidHom =
      BinaryLinear.parabolic BinaryNaturalDual.FourActors.A0Plane := by
  rw [Subgroup.map_equiv_normalizer_eq, S.four_A0_radical P]
  apply BinaryLinear.normalizer_radical
  intro he
  have hh := BinaryNaturalDual.FourActors.A0Plane_finrank
  rw [he,finrank_bot] at hh
  omega
end CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Stellmacher ChapterH.NaturalDual.SourceFourActors
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original Thompson image is a two-space radical, and its inner
normalizer is the corresponding parabolic. All quotient and Sylow markings
are those of the original chosen branch. -/
theorem doubleNatural_four_pure_thompson_parabolic_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      let P := (T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective;
      let J := ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf
        (normalizer (L : Set G))).map B.actionProjection;
      rank J = 4 ∧ IsElementaryAbelian 2 J ∧
        (J.subgroupOf (componentLayer B.ActionQuotient)).map
          (layerCoordinates S.setup P).toMonoidHom =
            BinaryLinear.radical BinaryNaturalDual.FourActors.A0Plane ∧
        (normalizer (J.subgroupOf (componentLayer B.ActionQuotient) :
          Set (componentLayer B.ActionQuotient))).map (layerCoordinates S.setup P).toMonoidHom =
            BinaryLinear.parabolic BinaryNaturalDual.FourActors.A0Plane := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  dsimp only
  rw [D.doubleNatural_four_pure_thompson_image_of_many h hmany B S w hw hp hfix hf]
  refine ⟨?_,actor_elementary S.setup _ 0,S.setup.four_A0_radical _,
    S.setup.four_A0_inner_normalizer _⟩
  unfold rank
  rw [actor_card S.setup _ 0]
  decide
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
