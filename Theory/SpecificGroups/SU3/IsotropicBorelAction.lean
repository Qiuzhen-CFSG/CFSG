module
public import BenderSuzuki.Converse.PSU3
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# The marked isotropic-point action of PSU₃

Huppert’s natural doubly transitive action has degree q³+1. Its coordinate
root and diagonal groups identify the distinguished point stabilizer with
the literal join of the projective unipotent and torus ranges. This retains
the exact Borel marking used by binary polar-orbit arguments.

Source: Huppert II.10.12.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.IsotropicBorelAction
variable {F : Type*} [Field F] [Finite F]

/-- The natural action, with the coordinate Borel as its point stabilizer. -/
theorem exists_action (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (q : ℕ)
    (hcard : Nat.card F = q^2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    Nat.card (BenderSuzuki.Converse.psuOmega J) = q^3+1 ∧
    ∃ (a : MulAction (ProjectiveSpecialUnitaryMatrixGroup J)
        (BenderSuzuki.Converse.psuOmega J)) (o : BenderSuzuki.Converse.psuOmega J),
      @MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) _ _ a o =
        (hermitianUnipotentPSU J hJ).range ⊔ (hermitianTorusPSU J hJ).range ∧
      @MulAction.IsMultiplyPretransitive (ProjectiveSpecialUnitaryMatrixGroup J)
        (BenderSuzuki.Converse.psuOmega J) _ a 2 := by
  obtain ⟨hc,ρ,o,_,_,_,hroot,htwo,_⟩ := huppert_II_10_12 J q hcard hfixed hJ
  obtain ⟨R,D,_,_,_,_,hsup,_,_,_,_,_,_,⟨coord,hcoord⟩,hD,hT⟩ := hroot
  have hcoord_eq (z : hermitianUnipotentCoord J) :
      (coord z).val = hermitianUnipotentPSU J hJ z := by
    obtain ⟨A,hA,he⟩ := hcoord z
    have hA' : A = hermitianUnipotentGL J z := Units.ext hA
    apply Subtype.ext
    simpa only [hA',hermitianUnipotentPSU_val] using he
  have hR : R = (hermitianUnipotentPSU J hJ).range := by
    apply le_antisymm
    · intro r hr
      obtain ⟨z,hz⟩ := coord.surjective ⟨r,hr⟩
      exact ⟨z,(hcoord_eq z).symm.trans (congrArg Subtype.val hz)⟩
    · rintro r ⟨z,rfl⟩
      rw [←hcoord_eq z]
      exact (coord z).property
  have hDeq : D = (hermitianTorusPSU J hJ).range := by
    apply le_antisymm
    · intro d hd
      obtain ⟨k,A,hA,he⟩ := hD ⟨d,hd⟩
      refine ⟨k,?_⟩
      have hA' : A = hermitianTorusGL J k := Units.ext hA
      apply Subtype.ext
      simpa only [hA',hermitianTorusPSU_val] using he.symm
    · rintro t ⟨k,rfl⟩
      obtain ⟨d,A,hA,he⟩ := hT k
      have hA' : A = hermitianTorusGL J k := Units.ext hA
      have hd : d.val = hermitianTorusPSU J hJ k := by
        apply Subtype.ext
        simpa only [hA',hermitianTorusPSU_val] using he
      rw [←hd]
      exact d.property
  let a : MulAction (ProjectiveSpecialUnitaryMatrixGroup J)
    (BenderSuzuki.Converse.psuOmega J) := MulAction.compHom _ ρ
  refine ⟨hc,a,o,?_,?_⟩
  · exact (hR ▸ hDeq ▸ hsup).symm
  · apply MulAction.is_two_pretransitive_iff.mpr
    intro x y z t hxy hzt
    exact htwo x y z t hxy hzt
end BenderSuzuki.MatrixGroups.HermitianForm.IsotropicBorelAction
