module
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourCartan

/-!
# The full native diagonal Cartan in Hermitian four-space

All diagonal special unitary matrices stabilize the native flag. The two
marked reflections normalize this set, and their native product has fourth
power one. This uses every diagonal entry, without restriction to the fixed
field; in particular it includes the full torusLift parameters.

These local identities feed the completion Cartan transport in
Aschbacher–Smith F.4.10,16–17, printed pp.279,282–283 of
`refs/quasithin.pdf`. They do not assert rigidity of native automorphisms.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourDiagonal
open UnitaryFourFlag UnitaryFourGeneration UnitaryFourSylow
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "J" => form F σ hσ

def IsDiagonal (g : SU F J) : Prop := ∃ d : Fin 4 → F, g.val.val=Matrix.diagonal d

omit [CharP F 2] in
theorem mem_borel (g : SU F J) (hg : IsDiagonal F σ hσ g) : g∈borelSU F J := by
  obtain ⟨d,hd⟩ := hg
  apply (mem_borel_iff_triangular F σ hσ g).mpr
  rw [hd]
  exact Matrix.blockTriangular_diagonal d

theorem point_conj (g : SU F J) (hg : IsDiagonal F σ hσ g) :
    IsDiagonal F σ hσ (middleSwap F σ hσ*g*(middleSwap F σ hσ)⁻¹) := by
  obtain ⟨d,hd⟩ := hg
  have hi : (middleSwap F σ hσ)⁻¹=middleSwap F σ hσ :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using FourCartan.middleSwap_sq F σ hσ)
  refine ⟨![d 0,d 2,d 1,d 3],?_⟩
  rw [hi]
  change (middleSwap F σ hσ).val.val*g.val.val*(middleSwap F σ hσ).val.val=_
  rw [hd]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [middleSwap,middleSwapMatrix,involutionElement,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]

theorem plane_conj (g : SU F J) (hg : IsDiagonal F σ hσ g) :
    IsDiagonal F σ hσ (pairSwap F σ hσ*g*(pairSwap F σ hσ)⁻¹) := by
  obtain ⟨d,hd⟩ := hg
  have hi : (pairSwap F σ hσ)⁻¹=pairSwap F σ hσ :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using FourCartan.pairSwap_sq F σ hσ)
  refine ⟨![d 1,d 0,d 3,d 2],?_⟩
  rw [hi]
  change (pairSwap F σ hσ).val.val*g.val.val*(pairSwap F σ hσ).val.val=_
  rw [hd]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairSwap,pairSwapMatrix,involutionElement,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]

theorem rotation_fourth : (FourCartan.rotation F σ hσ)^4=1 := by
  have hw : (FourCartan.rotation F σ hσ)^2=reverse F σ hσ := by
    simp only [FourCartan.rotation,pow_two,reverse,mul_assoc]
  calc
    _ = ((FourCartan.rotation F σ hσ)^2)^2 := pow_mul (FourCartan.rotation F σ hσ) 2 2
    _ = (reverse F σ hσ)^2 := by rw [hw]
    _ = reverse F σ hσ*(reverse F σ hσ)⁻¹ := by rw [UnitaryFourApartment.reverse_inv,pow_two]
    _ = 1 := mul_inv_cancel _
end Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourDiagonal
