module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourApartment

/-!
# The native unitary-four rotation centralizer

A native Borel element commuting with the quarter-turn also commutes with
its square, which reverses the flag. The two opposite flags force the
matrix to be diagonal. Rotation makes the four entries equal; determinant
one and characteristic two make that scalar one. The actual injective
SU₄ projection gives the same statement in PSU₄.

This is the native defect calculation for the Cartan route of
Aschbacher–Smith F.4.10,16–17, printed pp.279,282–283 of
`refs/quasithin.pdf`. It includes q = 4. It does not localize an arbitrary
full-extension completion defect in the native Borel.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups Subgroup
namespace Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourCartan
open UnitaryFourFlag UnitaryFourGeneration UnitaryFourApartment
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "J" => form F σ hσ

def rotation : SU F J := pairSwap F σ hσ * middleSwap F σ hσ

theorem pairSwap_sq : pairSwap F σ hσ ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  apply Units.ext
  change (pairSwapMatrix F) * (pairSwapMatrix F) = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairSwapMatrix,Matrix.mul_apply,Fin.sum_univ_succ]

theorem middleSwap_sq : middleSwap F σ hσ ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  apply Units.ext
  change (middleSwapMatrix F) * (middleSwapMatrix F) = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [middleSwapMatrix,Matrix.mul_apply,Fin.sum_univ_succ]

theorem rotation_matrix : (rotation F σ hσ).val.val =
    !![0,0,1,0; 1,0,0,0; 0,0,0,1; 0,1,0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation,pairSwap,middleSwap,involutionElement,pairSwapMatrix,middleSwapMatrix,
      Matrix.mul_apply,Fin.sum_univ_succ]

theorem diagonal_commute_rotation (g : SU F J)
    (hd : g.val.val = diagonal (fun i => g.val.val i i))
    (hr : Commute g (rotation F σ hσ)) : g = 1 := by
  let a : Fin 4 → F := fun i => g.val.val i i
  have he := congrArg (fun x : SU F J => x.val.val) hr.eq
  change g.val.val * (rotation F σ hσ).val.val =
    (rotation F σ hσ).val.val * g.val.val at he
  rw [hd,rotation_matrix] at he
  have h10 := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A 1 0) he
  have h31 := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A 3 1) he
  have h23 := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A 2 3) he
  simp [diagonal_mul,mul_diagonal] at h10 h31 h23
  have ha : ∀ i, a i = a 0 := by
    intro i
    fin_cases i
    · rfl
    · exact h10
    · exact h23.trans (h31.trans h10)
    · exact h31.trans h10
  have hdet : g.val.val.det = 1 := congrArg Units.val g.property.2
  rw [hd,Matrix.det_diagonal] at hdet
  change (∏ i, a i) = 1 at hdet
  simp only [ha,Fin.prod_univ_succ] at hdet
  have hp : a 0 ^ 4 = 1 := by simpa [pow_succ,mul_assoc] using hdet
  have ha1 : a 0 = 1 := by
    apply CharTwo.sq_injective
    apply CharTwo.sq_injective
    simpa only [←pow_mul,show 2*2=4 from rfl,one_pow] using hp
  apply Subtype.ext
  apply Units.ext
  change g.val.val = 1
  rw [hd]
  ext i j
  change diagonal a i j = (1 : Matrix (Fin 4) (Fin 4) F) i j
  simp [ha,ha1,Matrix.diagonal_apply,Matrix.one_apply]

theorem borel_commute_rotation (g : SU F J) (hg : g ∈ borelSU F J)
    (hr : Commute g (rotation F σ hσ)) : g = 1 := by
  apply diagonal_commute_rotation F σ hσ g
  · apply diagonal_of_opposite_flags F σ hσ g hg
    have hw : (rotation F σ hσ)^2 = reverse F σ hσ := by
      simp only [rotation,pow_two,UnitaryFourGeneration.reverse,mul_assoc]
    have hh : Commute g (reverse F σ hσ) := hw ▸ hr.pow_right 2
    have he : reverse F σ hσ * g * reverse F σ hσ = g := by
      calc
        _ = g * (reverse F σ hσ * (reverse F σ hσ)⁻¹) := by
          rw [reverse_inv,←hh.eq,mul_assoc]
        _ = g := by simp
    rwa [he]
  · exact hr
/-- The native projective Borel has trivial rotation centralizer. -/
theorem borel_project_commute_rotation (g : PSU F J)
    (hg : g ∈ (borelSU F J).map (project F J))
    (hr : Commute g (project F J (rotation F σ hσ))) : g = 1 := by
  obtain ⟨a,ha,rfl⟩ := hg
  have he : Commute a (rotation F σ hσ) :=
    (project_injective F J) (by simpa only [map_mul] using hr.eq)
  rw [borel_commute_rotation F σ hσ a ha he,map_one]

end Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourCartan
