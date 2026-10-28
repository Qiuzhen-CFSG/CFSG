module
public import Theory.SpecificGroups.SymmetricFourWreath.LocalStructure.Coordinates
public import Theory.SpecificGroups.SymmetricFourWreath.LocalStructure.Center

/-!
# The local centralizer of the marked diagonal involution

The double transposition has dihedral centralizer in S₄. Since the marked z
has that same entry in both base coordinates, its wreath centralizer is the
standard Sylow subgroup. This is the local identity used in source 13.9.5
and 13.9.8(2), printed pp.971–972 (PDF pp.988–989).
-/

public section
namespace SymmetricFourWreath
open Subgroup
private instance : DecidablePred (·∈square.range) := fun x=>
  inferInstanceAs (Decidable (∃a,square a=x))

theorem z_left (i : C2) : z.left i=square (DihedralGroup.r 2) := by
  revert i
  decide +kernel

private theorem z_right : z.right=1 := by decide +kernel

private theorem square_centralizer : ∀g:S4,
    g*square (DihedralGroup.r 2)=square (DihedralGroup.r 2)*g ↔ g∈square.range := by decide +kernel

theorem centralizer_z : centralizer ({z}:Set W)=(standardSylow:Subgroup W) := by
  ext x
  rw [mem_centralizer_singleton_iff,mem_standardSylow]
  constructor
  · intro h i
    apply (square_centralizer _).mp
    have he := congrArg (fun w:W=>w.left i) h
    simp only [RegularWreathProduct.mul_left,Pi.mul_apply,z_right,inv_one,one_mul] at he
    simpa only [z_left] using he
  · intro h
    apply RegularWreathProduct.ext
    · funext i
      simp only [RegularWreathProduct.mul_left,Pi.mul_apply,z_right,inv_one,one_mul]
      rw [z_left,z_left]
      exact (square_centralizer _).mpr (h i)
    · simp [z_right]
end SymmetricFourWreath
