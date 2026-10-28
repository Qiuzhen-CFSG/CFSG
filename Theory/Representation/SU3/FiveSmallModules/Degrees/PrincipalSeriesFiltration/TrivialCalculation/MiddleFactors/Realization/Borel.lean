module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Realization.Actors

/-!
# Matrix words for the full upper Borel

A short word in the specified actors gives the Weyl matrix. It produces two
upper root elements with linearly independent first coordinates and their
nontrivial central commutator. Small finite coordinate checks express every
root element as a product of powers of these three elements. The diagonal
actor covers the full torus. Thus their generated subgroup contains the
literal root-and-full-torus Borel, without computing the order of SU₃(5).

Source: `MiddleFactors/source/standard_flag_data.txt`; all word identities
are checked here, independently of the GAP diagnostic which found the word.
-/

@[expose] public section
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open BenderSuzuki.MatrixGroups.HermitianForm
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter
open BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Embedding
open Matrix
namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Realization
namespace BorelCertificate

abbrev form := FormTransport.standardForm tableForm
abbrev generated : Subgroup TableGroup := Subgroup.closure (Set.range tableActor)

def evalWord : List (Fin 2 × Bool) → TableGroup
  | [] => 1
  | (j, b) :: w => (if b then (tableActor j)⁻¹ else tableActor j) * evalWord w

theorem evalWord_mem (w : List (Fin 2 × Bool)) : evalWord w ∈ generated := by
  induction w with
  | nil => exact generated.one_mem
  | cons x w ih =>
    apply generated.mul_mem _ ih
    split
    · exact generated.inv_mem (Subgroup.subset_closure (Set.mem_range_self _))
    · exact Subgroup.subset_closure (Set.mem_range_self _)

/-- Signed letters [-1,2,-1,-2,-1,2,1,-2,1,1,2]. -/
def weylWord : TableGroup := evalWord
  [(0,true),(1,false),(0,true),(1,true),(0,true),(1,false),
    (0,false),(1,true),(0,false),(0,false),(1,false)]

theorem weylWord_matrix :
    ((weylWord : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) = hermitianWeylMatrix := by
  decide +kernel

def rootA : TableGroup := tableActor 1 * weylWord
def rootB : TableGroup := tableActor 0 * rootA * (tableActor 0)⁻¹
def rootC : TableGroup := rootA * rootB * rootA⁻¹ * rootB⁻¹

def matrixA : Matrix (Fin 3) (Fin 3) F25 := !![1,1,⟨0,4⟩; 0,1,-1; 0,0,1]
def matrixB : Matrix (Fin 3) (Fin 3) F25 := !![1,⟨4,2⟩,⟨0,3⟩; 0,1,⟨4,2⟩; 0,0,1]
def matrixC : Matrix (Fin 3) (Fin 3) F25 := !![1,0,⟨3,4⟩; 0,1,0; 0,0,1]

theorem rootA_matrix : ((rootA : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) = matrixA := by
  change tableActorMatrix 1 * (weylWord : GL (Fin 3) F25).val = matrixA
  rw [weylWord_matrix]
  decide +kernel

theorem rootB_matrix : ((rootB : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) = matrixB := by
  change (tableActor 0 : GL (Fin 3) F25).val * (rootA : GL (Fin 3) F25).val *
    ((tableActor 0)⁻¹ : GL (Fin 3) F25).val = matrixB
  rw [rootA_matrix]
  decide +kernel

def linearA : GL (Fin 3) F25 := GeneralLinearGroup.mkOfDetNeZero matrixA (by decide +kernel)
def linearB : GL (Fin 3) F25 := GeneralLinearGroup.mkOfDetNeZero matrixB (by decide +kernel)

theorem rootC_matrix : ((rootC : GL (Fin 3) F25) : Matrix (Fin 3) (Fin 3) F25) = matrixC := by
  have ha : (rootA : GL (Fin 3) F25) = linearA := Units.ext rootA_matrix
  have hb : (rootB : GL (Fin 3) F25) = linearB := Units.ext rootB_matrix
  change (rootA : GL (Fin 3) F25).val * (rootB : GL (Fin 3) F25).val *
    ((rootA : GL (Fin 3) F25)⁻¹).val * ((rootB : GL (Fin 3) F25)⁻¹).val = matrixC
  rw [ha, hb]
  decide +kernel

theorem rootA_mem : rootA ∈ generated :=
  generated.mul_mem (Subgroup.subset_closure (Set.mem_range_self 1)) (evalWord_mem _)

theorem rootB_mem : rootB ∈ generated :=
  generated.mul_mem (generated.mul_mem (Subgroup.subset_closure (Set.mem_range_self 0)) rootA_mem)
    (generated.inv_mem (Subgroup.subset_closure (Set.mem_range_self 0)))

theorem rootC_mem : rootC ∈ generated :=
  generated.mul_mem (generated.mul_mem (generated.mul_mem rootA_mem rootB_mem)
    (generated.inv_mem rootA_mem)) (generated.inv_mem rootB_mem)

def secondExponent (z : hermitianUnipotentCoord form) : ℕ := (3 * z.val.1.im).val
def firstExponent (z : hermitianUnipotentCoord form) : ℕ :=
  (z.val.1.re - 4 * (3 * z.val.1.im)).val
def centralExponent (z : hermitianUnipotentCoord form) : ℕ :=
  (4 * (z.val.2.im - ((matrixA ^ firstExponent z * matrixB ^ secondExponent z) 0 2).im)).val

/-- One check for each of the 125 actual upper-root coordinates. -/
theorem root_coordinates : ∀ z : hermitianUnipotentCoord form,
    hermitianUnipotentMatrix form z =
      matrixA ^ firstExponent z * matrixB ^ secondExponent z * matrixC ^ centralExponent z := by
  decide +kernel

/-- Every actual upper-root element belongs to the generated subgroup. -/
theorem root_mem (z : hermitianUnipotentCoord form) :
    hermitianUnipotentSU form rfl z ∈ generated := by
  have he : hermitianUnipotentSU form rfl z =
      rootA ^ firstExponent z * rootB ^ secondExponent z * rootC ^ centralExponent z := by
    apply Subtype.ext
    apply Units.ext
    change hermitianUnipotentMatrix form z =
      (rootA : GL (Fin 3) F25).val ^ firstExponent z *
        (rootB : GL (Fin 3) F25).val ^ secondExponent z *
          (rootC : GL (Fin 3) F25).val ^ centralExponent z
    rw [rootA_matrix, rootB_matrix, rootC_matrix]
    exact root_coordinates z
  rw [he]
  exact generated.mul_mem
    (generated.mul_mem (generated.pow_mem rootA_mem _) (generated.pow_mem rootB_mem _))
    (generated.pow_mem rootC_mem _)

def torusExponents : Array ℕ := #[0, 0, 18, 6, 12, 19, 10, 21, 14, 11, 13, 8, 4, 5, 15, 1, 3, 17, 16, 20, 7, 23, 2, 9, 22]

def torusExponent (k : F25ˣ) : ℕ := torusExponents[k.val.re.val + 5 * k.val.im.val]!

/-- The diagonal actor covers the full torus, not only a proper subtorus. -/
theorem torus_coordinates : ∀ k : F25ˣ,
    hermitianTorusMatrix form k = tableActorMatrix 0 ^ torusExponent k := by
  decide +kernel

theorem torus_mem (k : F25ˣ) : hermitianTorusSU form rfl k ∈ generated := by
  have he : hermitianTorusSU form rfl k = tableActor 0 ^ torusExponent k := by
    apply Subtype.ext
    apply Units.ext
    exact torus_coordinates k
  rw [he]
  exact generated.pow_mem (Subgroup.subset_closure (Set.mem_range_self 0)) _

end BorelCertificate

/-- The full literal Borel is contained in the subgroup generated by the two actors. -/
theorem tableBorel_le_generated : tableBorel ≤ Subgroup.closure (Set.range tableActor) := by
  apply sup_le
  · rintro _ ⟨z, rfl⟩
    exact BorelCertificate.root_mem z
  · rintro _ ⟨k, rfl⟩
    exact BorelCertificate.torus_mem k
end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Realization
