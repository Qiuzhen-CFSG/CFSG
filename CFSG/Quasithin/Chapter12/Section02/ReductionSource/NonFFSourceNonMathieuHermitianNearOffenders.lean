module
public import Theory.Representation.HermitianTensorThree.NearOffenders
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates

/-!
# The Hermitian (F-1)-offenders on the original chosen orbit

The literal automizer embedding and its component compatibility transfer
the complete near-offender calculation. Such an actor exists exactly when
n = 1. Every such actor has rank four and fixed codimension five, belongs
to the original component image, and is conjugate in the descended cover
to the concrete plane radical. The converse lifts the plane through the
same component map, rather than introducing an unrelated representation.

The two tensor applications construct their coordinates by descent from
the supplied inflated action. The original orbit, action and Sylow remain
unchanged. These prove the representation input for the alpha-column of
Table 7.2.1, including its field-four exception. They do not yet prove the
global bound r >= 4n: its odd-element and ambient centralizer inputs, the
bounds n <= w and k <= n, selection, and the source 8.2.3–13 exclusion
remain with qt-d-1222-nonmathieu-hermitian-exclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.4.4–5 and
the following alpha calculation, printed pp.381–382; Table 7.2.1 and 7.4.1,
printed pp.698–700 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
variable (n : ℕ) [NeZero n]
  (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
    (overgroupAction n (binaryImage n)))

/-- Every (F-1)-offender on the original automizer is the field-four
rank-four actor inside the original component image. -/
theorem sourceOrbit_hermitian_nearOffender
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (A : Subgroup (Automizer D.sourceOrbit)) (hA : IsElementaryTwo A)
    (hnear : fixedCodim (automizerRepresentation D.sourceOrbit) A ≤ rank A + 1) :
    n = 1 ∧ rank A = 4 ∧ fixedCodim (automizerRepresentation D.sourceOrbit) A = 5 ∧
      A ≤ D.hermitianComponentAutomizer.range ∧
      ∃ c : Cover n,
        (A.map (coordinateHom (automizerRepresentation D.sourceOrbit) n
          (D.hermitianOrbitCoordinates n d))).map
          (MulAut.conj (binaryActionHom n c)).toMonoidHom = UnipotentRadicals.plane n := by
  obtain ⟨j,hj,he,hcomp⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  let f := (binaryNormalizer n).subtype.comp j
  obtain ⟨hn,hr,hcod,hinner,hconj⟩ := NearOffenders.of_equivariant n
    (automizerRepresentation D.sourceOrbit) j hj (D.hermitianOrbitCoordinates n d) he A hA hnear
  have hf : f = coordinateHom (automizerRepresentation D.sourceOrbit) n
      (D.hermitianOrbitCoordinates n d) := by
    apply MonoidHom.ext
    intro a
    apply LinearEquiv.ext
    intro v
    rw [coordinateHom_apply]
    exact (congrArg (j a).val ((D.hermitianOrbitCoordinates n d).apply_symm_apply v)).symm.trans
      (he a ((D.hermitianOrbitCoordinates n d).symm v)).symm
  refine ⟨hn,hr,hcod,?_,?_⟩
  · intro a ha
    have hfa : f a ∈ binaryImage n := hinner (mem_map_of_mem f ha)
    obtain ⟨l,hl⟩ := (d.groupEquiv.surjective.comp D.orbitComponentHom_surjective) ⟨f a,hfa⟩
    exact ⟨l,hj (Subtype.ext ((hcomp l).trans (congrArg Subtype.val hl)))⟩
  · change ∃ c : Cover n, (A.map f).map
      (MulAut.conj (binaryActionHom n c)).toMonoidHom = UnipotentRadicals.plane n at hconj
    rwa [hf] at hconj

include d in
/-- The higher-field row has no (F-1)-offender on its literal automizer. -/
theorem sourceOrbit_hermitian_rank_add_one_lt_fixedCodim
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hn : 1 < n)
    (A : Subgroup (Automizer D.sourceOrbit)) (hA : IsElementaryTwo A) :
    rank A + 1 < fixedCodim (automizerRepresentation D.sourceOrbit) A := by
  by_contra hcod
  have he := (D.sourceOrbit_hermitian_nearOffender n d h A hA (Nat.le_of_not_gt hcod)).1
  omega

include d in
/-- The model calculation independently discharges the non-FF premise
for the actual full automizer, including at half-degree one. -/
theorem sourceOrbit_hermitian_automizer_not_isFFModule
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    ¬ IsFFModule (automizerRepresentation D.sourceOrbit) := by
  rintro ⟨A,hA,hcod⟩
  obtain ⟨_,hr,hc,_⟩ := D.sourceOrbit_hermitian_nearOffender n d h A hA
    (hcod.trans (Nat.le_add_right _ _))
  omega

/-- Descent from the supplied tensor marking proves the source alpha-row
alternative on the original subgroup and action, with no model callback. -/
theorem sourceOrbit_hermitian_tensor_nearOffender
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (A : Subgroup (Automizer D.sourceOrbit)) (hA : IsElementaryTwo A)
    (hnear : fixedCodim (automizerRepresentation D.sourceOrbit) A ≤ rank A + 1) :
    n = 1 ∧ rank A = 4 ∧ fixedCodim (automizerRepresentation D.sourceOrbit) A = 5 ∧
      A ≤ D.hermitianComponentAutomizer.range := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  obtain ⟨hn,hr,hc,hi,_⟩ := D.sourceOrbit_hermitian_nearOffender n d h A hA hnear
  exact ⟨hn,hr,hc,hi⟩


include d in
/-- The field-four plane supplies an actual exceptional actor in the original
automizer; every other half-degree excludes the whole (F-1) family. -/
theorem sourceOrbit_hermitian_exists_nearOffender_iff
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    (∃ A : Subgroup (Automizer D.sourceOrbit), IsElementaryTwo A ∧
      fixedCodim (automizerRepresentation D.sourceOrbit) A ≤ rank A + 1) ↔ n = 1 := by
  obtain ⟨j,hj,he,hcomp⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  apply NearOffenders.exists_iff_of_equivariant n (automizerRepresentation D.sourceOrbit)
    j hj (D.hermitianOrbitCoordinates n d) he
  intro a ha
  obtain ⟨l,hl⟩ := (d.groupEquiv.surjective.comp D.orbitComponentHom_surjective) ⟨a,ha⟩
  exact ⟨D.hermitianComponentAutomizer l,(hcomp l).trans (congrArg Subtype.val hl)⟩

/-- The original tensor marking both excludes and constructs (F-1)-offenders
at precisely the source half-degrees, retaining n = 1. -/
theorem sourceOrbit_hermitian_tensor_exists_nearOffender_iff
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    (∃ A : Subgroup (Automizer D.sourceOrbit), IsElementaryTwo A ∧
      fixedCodim (automizerRepresentation D.sourceOrbit) A ≤ rank A + 1) ↔ n = 1 := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  exact D.sourceOrbit_hermitian_exists_nearOffender_iff n d h

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
