module
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.SymplecticNatural
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Natural symplectic conjugation sections with an elementary central kernel

The symplectic group is transitive on nonzero natural vectors. One involutory
lift and a central elementary kernel therefore make every element of the
original group an involution. A noncentral elementary subgroup supplies that
lift. The coordinate map and actor remain the specified conjugation action.

Source: MS93 (3.6), final symplectic-case argument, printed p.871.
-/

public section
open Subgroup Representation
open Theory.SpecificGroups.SymplecticFour
namespace Representation.BinaryConjugationSection
variable {G F : Type*} [Group G] [Field F]
  [Algebra (ZMod 2) F] {H A B : Subgroup G}

/-- A central elementary kernel and a noncentral elementary seed force the
actual group to be elementary under the natural symplectic action. -/
theorem elementary_of_natural_symplectic
    (q : H →* Sp F) (hq : Function.Surjective q)
    (d : BinaryConjugationSection H A B
      ((restrictScalars (k := ZMod 2) (symplecticNatural 2)).comp q))
    (hcentral : B ≤ centralizer (A : Set G)) [IsElementaryAbelian 2 B]
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hEA : E ≤ A) (hEB : ¬ E ≤ B) :
    IsElementaryAbelian 2 A := by
  apply d.elementary_of_transitive hcentral
    (fun b hb => elemPow_eq_one_of_isElementaryAbelian b hb)
  · obtain ⟨e,he,heB⟩ := SetLike.not_le_iff_exists.mp hEB
    refine ⟨⟨e,hEA he⟩,Subtype.ext (elemPow_eq_one_of_isElementaryAbelian e he),?_⟩
    exact fun h => heB ((d.coordinates_eq_one_iff _).mp h)
  · intro v w hv hw
    obtain ⟨g,hg⟩ := TwoLocalCover.nonzero_vector_transitive hv hw
    obtain ⟨h,rfl⟩ := hq g
    exact ⟨h,hg⟩
end Representation.BinaryConjugationSection
