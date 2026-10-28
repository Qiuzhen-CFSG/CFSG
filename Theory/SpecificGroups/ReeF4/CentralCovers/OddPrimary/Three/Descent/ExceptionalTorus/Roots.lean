module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Descent.ExceptionalTorus.Algebraic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected.CorootWords

/-!
# The A₂×A₂ root and coroot marking

The long simple pair is α₀ = e₂-e₃ and β = -e₁-e₂. The short simple
pair is α₂ = e₄ and α₃ = (e₁-e₂-e₃-e₄)/2. Their Cartan matrix is
A₂×A₂. The lowest coroot has coordinates `(-2,-3,-2,-1)`.

The diagonal `diag(a,(a*b)⁻¹,b)` in the long A₂ factor is
`h_α₀(a) h_β(b⁻¹)`. Its exceptional companion contributes
`h_α₂((a*b)^s) h_α₃(b^s)`, where `s = (-2)^m`.
The proved all-root coroot-word formula identifies this literal product
with the faithful coordinate map, including its parameter-inversion convention.

Sources: GLS3 Example 2.6.3, Table 4.7.3A and §1.12; the all-root word
comparison is reused from the corrected concrete F₄ root model.
-/

@[expose] public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped Matrix
namespace ReeF4.CentralCovers.OddPrimary.Three.Descent.ExceptionalTorus
open ReeF4.CentralCovers.OddPrimary.Cyclotomic
open ReeF4.BinaryDegree.ExceptionalTensor
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected
noncomputable section

def lowestRoot : F4Chevalley.Root :=
  ⟨typeF4LowestRoot, typeF4LowestRoot_mem_typeF4Roots⟩

@[simp] theorem lowestRoot_val : (lowestRoot : Vec 4) = typeF4LowestRoot := rfl

theorem lowestRoot_long : IsLongRoot lowestRoot := by
  refine ⟨0, 1, by decide, -1, -1, by simp, by simp, ?_⟩
  ext i
  fin_cases i <;> simp [lowestRoot, typeF4LowestRoot, basisVector]

/-- The simple roots of the two orthogonal A₂ subsystems. -/
def subsystemRoots : Fin 4 → F4Chevalley.Root :=
  ![typeF4SimpleRootIndex 0, lowestRoot, typeF4SimpleRootIndex 2, typeF4SimpleRootIndex 3]

private theorem simple_scale (i : Fin 4) :
    typeF4CorootScale (typeF4SimpleRootIndex i) = if i.val < 2 then 1 else 2 := by
  simp only [typeF4CorootScale, typeF4SimpleRootIndex_mem_pair_iff]

/-- Its Cartan matrix is exactly A₂ × A₂, in the displayed order. -/
theorem subsystem_pairing (i j : Fin 4) :
    typeF4RootPairing.pairingIn ℤ (subsystemRoots i) (subsystemRoots j) =
      (!![2,-1,0,0; -1,2,0,0; 0,0,2,-1; 0,0,-1,2] : Matrix (Fin 4) (Fin 4) ℤ) i j := by
  have h := typeF4RootPairing.algebraMap_pairingIn ℤ (subsystemRoots i) (subsystemRoots j)
  simp only [algebraMap_int_eq, Int.coe_castRingHom] at h
  apply Int.cast_injective (α := ℝ)
  rw [h, typeF4RootPairing_pairing]
  have hl : typeF4CorootScale lowestRoot = 1 :=
    typeF4CorootScale_of_pair lowestRoot lowestRoot_long
  fin_cases i <;> fin_cases j <;>
    norm_num [subsystemRoots, simple_scale, hl, lowestRoot_val,
      typeF4LowestRoot, typeF4SimpleRootIndex_val, typeF4SimpleRoot, dot,
      Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]

theorem lowestRoot_corootCoordinates : corootCoordinates lowestRoot = ![-2,-3,-2,-1] := by
  have h (i : Fin 4) := corootCoordinates_pairing (typeF4SimpleRootIndex i) lowestRoot
  have hp (i : Fin 4) :
      typeF4RootPairing.pairingIn ℤ (typeF4SimpleRootIndex i) lowestRoot =
        ![-1,0,0,0] i := by
    have he := typeF4RootPairing.algebraMap_pairingIn ℤ (typeF4SimpleRootIndex i) lowestRoot
    simp only [algebraMap_int_eq, Int.coe_castRingHom] at he
    apply Int.cast_injective (α := ℝ)
    rw [he, typeF4RootPairing_pairing, typeF4CorootScale_of_pair lowestRoot lowestRoot_long]
    fin_cases i <;> norm_num [lowestRoot, typeF4LowestRoot, typeF4SimpleRootIndex_val,
      typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  have hs (i j : Fin 4) :
      F4Chevalley.torusRootExponent (typeF4SimpleRootIndex i) j = typeF4CartanMatrix i j :=
    typeF4RootPairing_base_cartan_apply i j
  simp only [Fin.sum_univ_four, hs, hp] at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  norm_num [typeF4CartanMatrix, Matrix.cons_val_two, Matrix.cons_val_three] at h0 h1 h2 h3
  ext i
  fin_cases i <;> dsimp <;> omega

variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]

/-- Conversion from the literal rank-one word to the inverse diagonal convention. -/
theorem coroot_diagonal (r : F4Chevalley.Root) (t : Fˣ) :
    algebraicCorootElement r t = diagonal (fun i => t ^ (-corootCoordinates r i)) := by
  let x : Variety.Point (KMult F) := (dPointEquiv 1).symm (fun _ => t)
  have hx : dPointEquiv 1 x 0 = t := by simp [x]
  rw [← hx, ← representationRootCocharacter_inclusion]
  rw [representationRootCocharacter, F4Chevalley.splitTorusCocharacter_inclusion_apply]
  apply congrArg (F4Chevalley.splitTorusMorphism (k := F)).onPoints
  apply (dPointEquiv 4).injective
  ext i
  simp [dCharacterTupleMorphism_apply]

/-- Four literal coroot words giving the marking of diag(a,(a*b)⁻¹,b). -/
def markedCorootWord (m : ℕ) (a b : Fˣ) : AlgebraicPoints F :=
  algebraicCorootElement (typeF4SimpleRootIndex 0) a *
    algebraicCorootElement lowestRoot b⁻¹ *
    algebraicCorootElement (typeF4SimpleRootIndex 2) ((a*b) ^ signedExponent m) *
    algebraicCorootElement (typeF4SimpleRootIndex 3) (b ^ signedExponent m)

theorem markedCorootWord_diagonal (m : ℕ) (a b : Fˣ) :
    markedCorootWord m a b = diagonal (coordinates m a b)⁻¹ := by
  simp only [markedCorootWord, coroot_diagonal, ← map_mul]
  congr 1
  ext i
  fin_cases i <;>
    simp [corootCoordinates_simple, lowestRoot_corootCoordinates, coordinates,
      zpow_add, mul_comm, mul_left_comm]

/-- The matrix map is the specified root/coroot marking, with its exact field transport. -/
theorem algebraicMap_corootWord (m : ℕ) (f : QuadraticField m →+* F) (a : Parameters m) :
    algebraicMap m f a =
      markedCorootWord m (normUnitHom m f a.1) (normUnitHom m f a.2) := by
  rw [markedCorootWord_diagonal]
  rfl

end
end ReeF4.CentralCovers.OddPrimary.Three.Descent.ExceptionalTorus
