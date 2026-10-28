module
public import Theory.Representation.ProjectiveFourTwoRank
public import BenderSuzuki.MatrixGroups.Unitary
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# The projective two-rank bound for odd unitary four-space

The actual projective special-unitary map has central kernel. The refined
central-quotient degree-four bound therefore gives two-rank at most five,
retaining the full matrix kernel and the literal map to PGL.
Source application: Aschbacher--Smith 4.4.3, printed p.622.
-/

public section
open Subgroup Matrix
namespace Theory.SpecificGroups.ClassicalUnitary
variable {F : Type*} [Field F] [Finite F]

/-- Every odd-characteristic projective special unitary four-space has two-rank at most five. -/
theorem odd_four_projective_twoRank_le_five
    (J : BenderSuzuki.MatrixGroups.HermitianForm 4 F) (h2 : (2 : F) ≠ 0) :
    primeRank 2 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) ≤ 5 := by
  let f := Matrix.ProjGenLinGroup.mk.subgroupMap J.specialSubgroup
  have hf : Function.Surjective f := Matrix.ProjGenLinGroup.mk.subgroupMap_surjective J.specialSubgroup
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective f hf
  have hc : f.ker ≤ center J.specialSubgroup := by
    intro x hx
    have hs : x.val ∈ center (GL (Fin 4) F) :=
      Matrix.ProjGenLinGroup.mk_eq_one.mp (congrArg Subtype.val (MonoidHom.mem_ker.mp hx))
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hs y.val)
  exact Representation.ProjectiveFour.central_quotient_twoRank_le_five
    J.specialSubgroup.subtype J.specialSubgroup.subtype_injective h2
    (fun s => s.property.2) f hf hc
end Theory.SpecificGroups.ClassicalUnitary
