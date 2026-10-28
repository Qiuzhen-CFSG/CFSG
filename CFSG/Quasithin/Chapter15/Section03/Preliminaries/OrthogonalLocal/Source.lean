module
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Baumann
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Thompson
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries

/-!
# The original orthogonal preliminary source family

The actual natural action supplies every finite geometry input to the source
Sylow, Thompson and central-omega arguments. The full two-residual alternative
uses the actual Sylow image; the noncentral Thompson calculation and both
local odd indices yield the two ambient Sylow conclusions. The same fixed
plane is then identified with the central involutions of its stabilizer.

These are the original 15.3.2(4), 15.3.5--6 and 15.3.8 consumers. The natural
action is the preceding 15.1.3 conclusion and the ordering maximum and Baumann
normalizer control come from 14.1.11--12/15.3.3. No model geometry, image,
Thompson, index or central-omega conclusion remains an additional input.
Source: Aschbacher--Smith, printed pp.1121--1122.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03
open Subgroup Stellmacher ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original two-residual alternative, with the actual Sylow image maximality proved. -/
theorem source_lemma_15_3_2_4
    (T : Sylow 2 G) {M X : Subgroup G}
    (d : NaturalOrthogonalAction M (localModule T M))
    (hM : IsOrderingMaximal T M) (hTX : (T : Subgroup G) ≤ X) (hXM : X ≤ M) :
    twoResidualAmbient X ≤ M ⊓ centralizer (localModule T M : Set G) ∨
      (d.image X = ⊤ ∧ Chapter4.UniqueMaximalOvergroup X M) :=
  lemma_15_3_2_4_of_sylow_image_maximal T d hM
    (d.image_sylow_isCoatom T hM.1.2) hTX hXM

/-- The actual Thompson alternatives, including every isomorphism and intersection. -/
theorem source_lemma_15_3_5
    (T : Sylow 2 G) {M : Subgroup G}
    (d : NaturalOrthogonalAction M (localModule T M))
    (hM : IsOrderingMaximal T M) (i : OrthogonalPlaneIndex) :
    (⁅localModule T M, elementaryAbelianMaxJ (T : Subgroup G)⁆ = ⊥ ∧
      ChapterB.baumann (T : Subgroup G) =
        ChapterB.baumann ((T : Subgroup G) ⊓ centralizer (localModule T M : Set G)) ∧
      localModule T M ≤ ChapterB.thompsonAlpha (T : Subgroup G) ∧
      (ChapterB.baumann (T : Subgroup G)).characteristicNormalizerClosure ≤ M) ∨
    (d.image (ChapterB.baumann (T : Subgroup G)) =
        d.image (elementaryAbelianMaxJ (T : Subgroup G)) ∧
      d.image (elementaryAbelianMaxJ (T : Subgroup G)) =
        d.image (planeStabilizer T (d.plane i)) ∧
      Nonempty (d.image (planeStabilizer T (d.plane i)) ≃* OrthogonalPlaneVector) ∧
      ChapterB.thompsonAlpha (T : Subgroup G) ⊓ localModule T M =
        fixedPlane (localModule T M) (planeStabilizer T (d.plane i)) ∧
      Nonempty (fixedPlane (localModule T M) (planeStabilizer T (d.plane i)) ≃*
        OrthogonalPlaneVector) ∧
      ChapterB.baumann (T : Subgroup G) ≤ planeStabilizer T (d.plane i)) := by
  by_cases hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)
  · exact Or.inl (lemma_15_3_5_centralizing T d hM hJ)
  · exact Or.inr (orthogonal_noncentral_of_geometry T d hM.1.2 i hJ
      (d.elementary_image_planeStabilizer T hM.1.2 i)
      (d.card_image_planeStabilizer T hM.1.2 i)
      (d.card_fixedPlane_planeStabilizer T hM.1.2 i))

/-- The actual Baumann subgroup preserves both original definite planes. -/
theorem source_baumann_le_planeStabilizer
    (T : Sylow 2 G) {M : Subgroup G}
    (d : NaturalOrthogonalAction M (localModule T M))
    (hM : IsOrderingMaximal T M) (i : OrthogonalPlaneIndex) :
    ChapterB.baumann (T : Subgroup G) ≤ planeStabilizer T (d.plane i) := by
  by_cases hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)
  · exact baumann_le_planeStabilizer_of_centralizing T d hM hJ i
  · exact (orthogonal_noncentral_of_geometry T d hM.1.2 i hJ
      (d.elementary_image_planeStabilizer T hM.1.2 i)
      (d.card_image_planeStabilizer T hM.1.2 i)
      (d.card_fixedPlane_planeStabilizer T hM.1.2 i)).2.2.2.2.2

/-- Every original 15.3.6 conclusion, with the local Sylow indices discharged. -/
theorem source_lemma_15_3_6
    (T : Sylow 2 G) {M : Subgroup G}
    (d : NaturalOrthogonalAction M (localModule T M))
    (hM : IsOrderingMaximal T M)
    (hN : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M)
    (i : OrthogonalPlaneIndex) :
    ChapterB.baumann (T : Subgroup G) = ChapterB.baumann (planeStabilizer T (d.plane i)) ∧
      (normalizer (planeStabilizer T (d.plane i) : Set G) ≤
        normalizer (ChapterB.baumann (planeStabilizer T (d.plane i)) : Set G) ∧
      normalizer (ChapterB.baumann (planeStabilizer T (d.plane i)) : Set G) ≤ M) ∧
      (∃ P : Sylow 2 (centralizer (fixedPlane (d.plane i) (planeStabilizer T (d.plane i)) : Set G)),
        (P : Subgroup _).map (centralizer (fixedPlane (d.plane i) (planeStabilizer T (d.plane i)) : Set G)).subtype =
          planeStabilizer T (d.plane i)) ∧
      (∃ P : Sylow 2 (normalizer (d.plane i : Set G)),
        (P : Subgroup _).map (normalizer (d.plane i : Set G)).subtype = planeStabilizer T (d.plane i)) :=
  lemma_15_3_6_of_local_indices T (d.plane i) M
    (source_baumann_le_planeStabilizer T d hM i) hN
    (d.not_dvd_planeStabilizer_centralizer_relIndex T hM.1.2 i)
    (d.not_dvd_planeStabilizer_normalizer_relIndex T hM.1.2 i)

/-- The source central omega equality on the literal stabilizer and its fixed plane. -/
theorem source_lemma_15_3_8
    (T : Sylow 2 G) {M : Subgroup G}
    (d : NaturalOrthogonalAction M (localModule T M))
    (hTM : (T : Subgroup G) ≤ M) (i : OrthogonalPlaneIndex) :
    fixedPlane (localModule T M) (planeStabilizer T (d.plane i)) =
        centralOmegaIn (planeStabilizer T (d.plane i)) ∧
      Nonempty (fixedPlane (localModule T M) (planeStabilizer T (d.plane i)) ≃* OrthogonalPlaneVector) := by
  let := d.elementary_fixedPlane (planeStabilizer T (d.plane i))
  exact lemma_15_3_8_of_plane_facts T (localModule T M) (d.plane i)
    (d.planeStabilizer_index_two T hTM i) (d.card_centralInvolutions T hTM)
    (d.fixedPlane_le_stabilizer T hTM (localModule_le T hTM) i)
    (d.card_fixedPlane_planeStabilizer T hTM i)

end CFSG.Quasithin.Chapter15.Section03
