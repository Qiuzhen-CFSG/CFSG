module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Counts
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Models
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourValence
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointIndex
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.LineCore
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.PlaneCore
public import Theory.GroupAction.RankTwoCosetGeometry.PathOrderLowerBound

/-!
# Valencies of the actual projective unitary coset geometries

The native four-space transversals give point degree q+1 and plane degree
q²+1. The marked whole-overlap covers transport these degrees to every
faithful completion of a full source extension, including even outer degree.
For the fixed PSU₅(4) model the existing projective flag indices give degrees
65 and 17, with the actual scalar quotient retained throughout.

Source: Aschbacher–Smith F.4.5, F.4.13 and F.4.24, printed pp.275, 280 and287.
These are local counts, not a Hermitian recognition assertion.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry hiding Vertex base
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.BasedWalk
open GreenBook.LieModels.UnitaryFour Theory.SpecificGroups.ClassicalUnitary

/-- The two actual U₄ flag indices, in point/plane order. -/
def fourDegree (m : ℕ) (i : Bool) : ℕ := if i then (2^m)^2+1 else 2^m+1

/-- The full projective overlap has the native relative index at each endpoint. -/
theorem four_local_index (m : ℕ) (hm : 1 ≤ m) (i : Bool) :
    ((SourceExtension.nativeFamily (P₀ := pointParabolic m hm)
        (P₁ := planeParabolic m hm) (!i)).subgroupOf
      (SourceExtension.nativeFamily (P₀ := pointParabolic m hm)
        (P₁ := planeParabolic m hm) i)).index = fourDegree m i := by
  cases i
  · change ((planeParabolic m hm).subgroupOf (pointParabolic m hm)).index = 2^m+1
    rw [← inf_subgroupOf_left, exact_overlap]
    change ((overlapMatrix m hm).map (projection m hm)).relIndex
      ((pointParabolicMatrix m hm).map (projection m hm)) = _
    rw [relIndex_map_map_of_injective _ _ (projection_injective m hm)]
    exact (SmallCompletion.FourValence.point_index (MatrixField m) (fieldConj m)
      (fieldConj_involutive m hm)).trans (congrArg (· + 1) (PointLocal.fixedField_card m hm))
  · change ((pointParabolic m hm).subgroupOf (planeParabolic m hm)).index = (2^m)^2+1
    rw [← inf_subgroupOf_right, exact_overlap]
    change ((overlapMatrix m hm).map (projection m hm)).relIndex
      ((planeParabolicMatrix m hm).map (projection m hm)) = _
    rw [relIndex_map_map_of_injective _ _ (projection_injective m hm)]
    exact (SmallCompletion.FourValence.plane_index (MatrixField m) (fieldConj m)
      (fieldConj_involutive m hm)).trans (congrArg (· + 1) (matrixField_card m hm))

/-- Native valence is q+1 at points and q²+1 at planes. -/
theorem four_native_card_neighbors (m : ℕ) (hm : 1 ≤ m)
    (v : Vertex (SourceExtension.nativeFamily (P₀ := pointParabolic m hm)
      (P₁ := planeParabolic m hm))) :
    Nat.card ((graph (SourceExtension.nativeFamily (P₀ := pointParabolic m hm)
      (P₁ := planeParabolic m hm))).neighborSet v) = fourDegree m v.type :=
  card_neighbors_of_indices _ (fourDegree m) (four_local_index m hm) v

/-- The valence calculation survives every faithful full-extension completion
with the literal whole overlap, including even outer degree. -/
theorem four_completion_card_neighbors (m : ℕ) (hm : 1 ≤ m) (E : FourExtension m hm)
    {M : Type*} [Group M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (v : Vertex c.cosetFamily) :
    Nat.card ((graph c.cosetFamily).neighborSet v) = fourDegree m v.type := by
  obtain ⟨a,ha⟩ := exists_smul_base c.cosetFamily v
  have he := Nat.card_congr ((translationGraphIso c.cosetFamily a).mapNeighborSet
    (base c.cosetFamily v.type))
  change Nat.card ((graph c.cosetFamily).neighborSet (base c.cosetFamily v.type)) =
    Nat.card ((graph c.cosetFamily).neighborSet (a • base c.cosetFamily v.type)) at he
  rw [ha] at he
  exact he.symm.trans ((E.completion_card_neighbors_eq_native (four_conj_injective m hm)
    (parabolics_generate m hm) c hoverlap v.type).trans
      (four_native_card_neighbors m hm (base _ v.type)))

/-- The exceptional source model has valences 65 and 17 on its actual
projective flag cosets; the SU₅ scalar kernel has not been discarded. -/
theorem five_native_card_neighbors (U : GreenBook.UnitaryFive.Model 4)
    (v : Vertex (SourceExtension.nativeFamily (P₀ := U.leftParabolic)
      (P₁ := U.rightParabolic))) :
    Nat.card ((graph (SourceExtension.nativeFamily (P₀ := U.leftParabolic)
      (P₁ := U.rightParabolic))).neighborSet v) = if v.type then 17 else 65 := by
  apply card_neighbors_of_indices _ (fun i => if i then 17 else 65) _ v
  intro i
  cases i
  · change (U.rightParabolic.subgroupOf U.leftParabolic).index = 65
    rw [← inf_subgroupOf_left]
    exact U.overlap_index_eq_sixtyFive
  · change (U.leftParabolic.subgroupOf U.rightParabolic).index = 17
    rw [← inf_subgroupOf_right]
    exact U.overlap_rightParabolic_index

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
