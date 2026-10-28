module
public import Theory.Combinatorics.TranslationPlane.ProjectiveActions
public import Theory.Combinatorics.TranslationPlane.FlagElations
public import Theory.SpecificGroups.LinearHigher.Presentation

/-!
# Elementary matrices as literal projective flag elations

The root 1+aEᵢⱼ fixes the hyperplane xⱼ=0 pointwise and every line through
[eᵢ]. The point and inverse-transpose line actions are both retained.
These identities connect the full geometric flag groups to all six native
A₂ roots and all orientations of the elementary presentation relations.

Source: Steinberg, Lectures on Chevalley Groups, Section 6, SL example;
DGS, Groups and Graphs, Theorem D, printed p.224.
-/

@[expose] public noncomputable section
namespace Configuration.TranslationPlane.FieldChart
open Matrix Projectivization Theory.SpecificGroups.LinearHigher
open scoped MatrixGroups
variable (F : Type*) [Field F]

/-- A coordinate point, or the matching coordinate hyperplane covector. -/
def coordinate (i : Fin 3) : PG F :=
  mk F (Pi.single i 1) (by intro h; have := congrFun h i; simp at this)

theorem coordinate_incident {i j : Fin 3} (hij : i ≠ j) :
    coordinate F i ∈ coordinate F j := by
  simp [coordinate,ofField.mem_iff,orthogonal_mk,dotProduct_single,hij.symm]

/-- Every native matrix root lies in its full incidence flag-elation subgroup. -/
theorem matrixRoot_mem_flagElations (r : Root 3) (a : F) :
    specialLinearCollineation (matrixRoot r a) ∈
      flagElations (coordinate F r.val.1) (coordinate F r.val.2) := by
  constructor
  · intro p hp
    induction p using Projectivization.ind with | h v hv =>
    have hvj : v r.val.2 = 0 := by
      simpa [coordinate,ofField.mem_iff,orthogonal_mk,dotProduct_single] using hp
    rw [specialLinearCollineation_point,smul_mk]
    have hvec : matrixRoot r a • v = v := by
      change (matrixRoot r a).val *ᵥ v = v
      simp [matrixRoot,SpecialLinearGroup.transvection_coe,add_mulVec,single_mulVec_eq,hvj]
    exact congrArg (fun x : {v : Fin 3 → F // v ≠ 0} => Projectivization.mk' F x)
      (Subtype.ext hvec)
  · intro m hm
    induction m using Projectivization.ind with | h v hv =>
    have hvi : v r.val.1 = 0 := by
      simpa [coordinate,ofField.mem_iff,orthogonal_mk,single_dotProduct] using hm
    rw [specialLinearCollineation_line,smul_mk]
    have hvec : SpecialLinearGroup.inverseTranspose (matrixRoot r a) • v = v := by
      change (matrixRoot r a)⁻¹.val.transpose *ᵥ v = v
      rw [matrixRoot,SpecialLinearGroup.transvection_inv]
      simp [SpecialLinearGroup.transvection_coe,transpose_add,transpose_single,
        add_mulVec,single_mulVec_eq,hvi]
    exact congrArg (fun x : {v : Fin 3 → F // v ≠ 0} => Projectivization.mk' F x)
      (Subtype.ext hvec)

end Configuration.TranslationPlane.FieldChart
