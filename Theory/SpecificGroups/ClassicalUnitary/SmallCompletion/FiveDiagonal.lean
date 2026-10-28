module
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FiveFixed

/-!
# The full native diagonal Cartan in Hermitian five-space

In the actual hyperbolic coordinates, all diagonal special unitary matrices
stabilize the native point and plane. Both marked reflections normalize
this set. The projective consumer takes its image under SU₅ → PSU₅, keeping
the scalar kernel; no injectivity of that map is used.

These identities feed the completion Cartan transport in Aschbacher–Smith
F.4.10,16–17, printed pp.279,282–283 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryFive.SmallCompletion.FiveDiagonal
open PlaneCore FivePaths
variable {F : Type*} [Field F] [CharP F 2]
variable (J : HermitianForm 5 F) (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)

def IsDiagonal (g : J.specialSubgroup) : Prop :=
  ∃ d : Fin 5 → F, (coordinates J c g).val=diagonal d

theorem mem_flag [Finite F] (g : J.specialSubgroup) (hg : IsDiagonal J c g) :
    g∈specialStabilizer J (line F) ⊓ specialStabilizer J (plane F) := by
  obtain ⟨d,hd⟩ := hg
  constructor
  · apply (FiveFixed.mem_line_iff J c g).mpr
    intro i hi
    rw [hd,diagonal_apply_ne _ hi]
  · apply (FiveFixed.mem_plane_iff J c g).mpr
    intro i j hi hj
    rw [hd,diagonal_apply_ne _ (by rcases hi with rfl | rfl | rfl <;>
      rcases hj with rfl | rfl <;> decide)]

theorem point_conj (g : J.specialSubgroup) (hg : IsDiagonal J c g) :
    IsDiagonal J c (middleSwap J c hc hJ*g*(middleSwap J c hc hJ)⁻¹) := by
  obtain ⟨d,hd⟩ := hg
  have hi : (middleSwap J c hc hJ)⁻¹=middleSwap J c hc hJ :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using middleSwap_sq J c hc hJ)
  refine ⟨![d 0,d 4,d 2,d 3,d 1],?_⟩
  rw [hi,map_mul,map_mul,coordinates_middleSwap]
  change (blockPerm middlePerm).val*(coordinates J c g).val*(blockPerm middlePerm).val=_
  rw [hd,middle_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]

theorem plane_conj (g : J.specialSubgroup) (hg : IsDiagonal J c g) :
    IsDiagonal J c (pairSwap J c hc hJ*g*(pairSwap J c hc hJ)⁻¹) := by
  obtain ⟨d,hd⟩ := hg
  have hi : (pairSwap J c hc hJ)⁻¹=pairSwap J c hc hJ :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using pairSwap_sq J c hc hJ)
  refine ⟨![d 1,d 0,d 2,d 4,d 3],?_⟩
  rw [hi,map_mul,map_mul,coordinates_pairSwap]
  change (blockPerm pairPerm).val*(coordinates J c g).val*(blockPerm pairPerm).val=_
  rw [hd,pair_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]
end Theory.SpecificGroups.UnitaryFive.SmallCompletion.FiveDiagonal
