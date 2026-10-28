module

public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.UnipotentGeometry

/-!
# The split Cartan and the Borel-preserving graph action in PSL₃

The torus consists of the actual projective images of diagonal matrices
`diag(a, (ab)⁻¹, b)`. Field automorphisms act on the two unit parameters.
The longest Weyl element adjusts inverse transpose to preserve the upper
unitriangular subgroup; it swaps and inverts the two torus parameters.
In characteristic two this adjusted graph automorphism squares to one.

These calculations concern the specified matrix subgroups. Conjugating a
source Cartan to this torus and factoring its normalizer are separate steps.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.15(5),
printed pp.50–51, and the proof of 1.3.4, printed p.511; GLS3, §2.7.
The imported projective coefficient transport retains its ATLAS attribution.
-/

@[expose] public section

open scoped MatrixGroups
open Matrix Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
namespace Matrix.PSL3.CartanActions
variable (F : Type*) [Field F]

def torusSL : (Fˣ × Fˣ) →* SL(3,F) where
  toFun d := ⟨diagonal ![(d.1 : F), ((d.1 * d.2)⁻¹ : Fˣ), (d.2 : F)], by
    simp [det_diagonal, Fin.prod_univ_three, mul_comm]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    change diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc]

def torusMap : (Fˣ × Fˣ) →* PSL(3,F) := (projection F).comp (torusSL F)
def torus : Subgroup PSL(3,F) := (torusMap F).range

theorem torusSL_val (d : Fˣ × Fˣ) :
    (torusSL F d).val = diagonal ![(d.1 : F), ((d.1 * d.2)⁻¹ : Fˣ), (d.2 : F)] := rfl

theorem torus_le_borel [Finite F] : torus F ≤ borel F := by
  rintro _ ⟨d, rfl⟩
  apply Subgroup.mem_map_of_mem
  rw [mem_borelSL_iff, torusSL_val]
  simp

theorem field_torusMap (σ : F ≃+* F) (d : Fˣ × Fˣ) :
    fieldAction F σ (torusMap F d) =
      torusMap F (Units.map σ.toMonoidHom d.1, Units.map σ.toMonoidHom d.2) := by
  change fieldAction F σ (QuotientGroup.mk (torusSL F d)) = QuotientGroup.mk _
  rw [fieldAction_mk]
  apply congrArg (QuotientGroup.mk : SL(3,F) → PSL(3,F))
  apply Subtype.ext
  simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, torusSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- A uniform power formula on the field gives the same formula on the torus. -/
theorem field_torus_power_of (σ : F ≃+* F) (k : ℕ) (hk : ∀ x, σ x = x ^ k) :
    ∀ x ∈ torus F, fieldAction F σ x = x ^ k := by
  rintro _ ⟨d, rfl⟩
  rw [field_torusMap, ← map_pow]
  congr 1
  apply Prod.ext <;> apply Units.ext <;> exact hk _

def reversalSL [CharP F 2] : SL(3,F) :=
  ⟨(reversalGL F).val, by simp [reversalGL, Matrix.det_fin_three, CharTwo.neg_eq]⟩

theorem reversalSL_toGL [CharP F 2] : SpecialLinearGroup.toGL (reversalSL F) = reversalGL F :=
  Units.ext rfl

theorem reversalSL_sq [CharP F 2] : reversalSL F ^ 2 = 1 := by
  apply SpecialLinearGroup.toGL_injective
  rw [map_pow, reversalSL_toGL, map_one, pow_two]
  apply Units.ext
  change (reversalGL F).val * (reversalGL F).val = 1
  exact (reversalGL F).val_inv

theorem graph_reversal [CharP F 2] : graph F (projection F (reversalSL F)) =
    projection F (reversalSL F) := by
  change graph F (QuotientGroup.mk (reversalSL F)) = QuotientGroup.mk _
  rw [graph_mk]
  have ht : SpecialLinearGroup.transpose (reversalSL F) = reversalSL F := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [ht]
  congr 1
  exact inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using reversalSL_sq F)

theorem oppositionGraph_sq [CharP F 2] : oppositionGraph F ^ 2 = 1 := by
  have he : oppositionGraph F = MulAut.conj (projection F (reversalSL F)) * graph F := by
    rw [oppositionGraph, ← reversalSL_toGL, linearConj_toGL]
    rfl
  rw [he]
  apply MulEquiv.ext
  intro x
  change projection F (reversalSL F) *
    graph F (projection F (reversalSL F) * graph F x * (projection F (reversalSL F))⁻¹) *
    (projection F (reversalSL F))⁻¹ = x
  have hg : graph F (graph F x) = x := DFunLike.congr_fun (graph_sq F) x
  have hw : projection F (reversalSL F) * projection F (reversalSL F) = 1 := by
    rw [← map_mul]
    simpa only [pow_two, map_one] using congrArg (projection F) (reversalSL_sq F)
  rw [map_mul, map_mul, map_inv, graph_reversal, hg]
  calc
    _ = (projection F (reversalSL F) * projection F (reversalSL F)) * x *
        (projection F (reversalSL F) * projection F (reversalSL F))⁻¹ := by group
    _ = x := by rw [hw]; simp

theorem graphSL_torusSL (d : Fˣ × Fˣ) :
    graphSL F (torusSL F d) = torusSL F d⁻¹ := by
  change (SpecialLinearGroup.transpose (torusSL F d))⁻¹ = _
  have ht : SpecialLinearGroup.transpose (torusSL F d) = torusSL F d := by
    apply Subtype.ext
    simp [torusSL_val]
  rw [ht, map_inv]

theorem linearConjSL_reversal_torusSL (d : Fˣ × Fˣ) :
    linearConjSL F (reversalGL F) (torusSL F d) = torusSL F (d.2, d.1) := by
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL]
  apply Units.ext
  change (reversalGL F).val * (torusSL F d).val * (reversalGL F).inv = _
  rw [torusSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reversalGL, torusSL_val, Matrix.vecMul, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_three, mul_comm]

theorem oppositionGraph_torusMap (d : Fˣ × Fˣ) :
    oppositionGraph F (torusMap F d) = torusMap F (d.2⁻¹, d.1⁻¹) := by
  change QuotientGroup.mk (linearConjSL F (reversalGL F) (graphSL F (torusSL F d))) = _
  rw [graphSL_torusSL, linearConjSL_reversal_torusSL]
  rfl

theorem oppositionGraph_torus :
    (torus F).map (oppositionGraph F).toMonoidHom = torus F := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩
    exact ⟨(d.2⁻¹,d.1⁻¹), (oppositionGraph_torusMap F d).symm⟩
  · rintro _ ⟨d, rfl⟩
    refine ⟨torusMap F (d.2⁻¹,d.1⁻¹), ⟨_,rfl⟩, ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      oppositionGraph_torusMap, inv_inv]

theorem torus_isMulCommutative : IsMulCommutative (torus F) := by
  refine ⟨⟨?_⟩⟩
  rintro ⟨_,a,rfl⟩ ⟨_,b,rfl⟩
  apply Subtype.ext
  exact (map_mul (torusMap F) a b).symm.trans
    ((congrArg (torusMap F) (mul_comm a b)).trans (map_mul (torusMap F) b a))

theorem reversal_conj_val (x : SL(3,F)) (i j : Fin 3) :
    (linearConjSL F (reversalGL F) x).val i j = x.val i.rev j.rev := by
  have h := congrArg Units.val (linearConjSL_toGL F (reversalGL F) x)
  change (linearConjSL F (reversalGL F) x).val =
    (reversalGL F).val * x.val * (reversalGL F).inv at h
  rw [h]
  fin_cases i <;> fin_cases j <;>
    simp [reversalGL, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

theorem reversal_transpose_mem_unipotentSL (x : SL(3,F)) (hx : x ∈ unipotentSL F) :
    linearConjSL F (reversalGL F) (SpecialLinearGroup.transpose x) ∈ unipotentSL F := by
  obtain ⟨h00,h10,h20⟩ := (mem_pointLocalSL_iff F x).mp hx.1
  obtain ⟨_,h21,h22⟩ := (mem_lineLocalSL_iff F x).mp hx.2
  rw [unipotentSL, Subgroup.mem_inf, mem_pointLocalSL_iff, mem_lineLocalSL_iff]
  simp only [reversal_conj_val, SpecialLinearGroup.coe_transpose, Matrix.transpose_apply]
  exact ⟨⟨h22,h21,h20⟩,⟨h20,h10,h00⟩⟩

theorem oppositionGraph_mem_unipotent {x : PSL(3,F)} (hx : x ∈ unipotent F) :
    oppositionGraph F x ∈ unipotent F := by
  obtain ⟨y,hy,rfl⟩ := hx
  change projection F (linearConjSL F (reversalGL F) (SpecialLinearGroup.transpose y)⁻¹) ∈ _
  rw [map_inv]
  exact Subgroup.mem_map_of_mem _
    ((unipotentSL F).inv_mem (reversal_transpose_mem_unipotentSL F y hy))

theorem oppositionGraph_unipotent [CharP F 2] :
    (unipotent F).map (oppositionGraph F).toMonoidHom = unipotent F := by
  apply le_antisymm
  · rintro _ ⟨y,hy,rfl⟩
    exact oppositionGraph_mem_unipotent F hy
  · intro y hy
    refine ⟨oppositionGraph F y, oppositionGraph_mem_unipotent F hy, ?_⟩
    exact DFunLike.congr_fun (oppositionGraph_sq F) y

theorem fieldAction_mem_unipotent (σ : F ≃+* F) {x : PSL(3,F)}
    (hx : x ∈ unipotent F) : fieldAction F σ x ∈ unipotent F := by
  obtain ⟨y,hy,rfl⟩ := hx
  change fieldAction F σ (QuotientGroup.mk y) ∈ _
  rw [fieldAction_mk]
  apply Subgroup.mem_map_of_mem (projection F)
  obtain ⟨h00,h10,h20⟩ := (mem_pointLocalSL_iff F y).mp hy.1
  obtain ⟨_,h21,h22⟩ := (mem_lineLocalSL_iff F y).mp hy.2
  rw [unipotentSL, Subgroup.mem_inf, mem_pointLocalSL_iff, mem_lineLocalSL_iff]
  simp [SpecialLinearGroup.map_apply_coe, h00,h10,h20,h21,h22]

theorem fieldAction_unipotent (σ : F ≃+* F) :
    (unipotent F).map (fieldAction F σ).toMonoidHom = unipotent F := by
  apply le_antisymm
  · rintro _ ⟨y,hy,rfl⟩
    exact fieldAction_mem_unipotent F σ hy
  · intro y hy
    refine ⟨fieldAction F σ⁻¹ y, fieldAction_mem_unipotent F σ⁻¹ hy, ?_⟩
    change (fieldAction F σ * fieldAction F σ⁻¹) y = y
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl

end Matrix.PSL3.CartanActions
