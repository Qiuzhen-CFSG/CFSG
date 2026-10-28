module

public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental.CentralizerResidual.Generation.Reduction

/-!
# Norm-normalized special unitary plane rotations

For σ(a)a + σ(b)b = 1, the matrix with rows (σ(a), σ(b)) and (-b, a)
is in the actual identity-form SU₂ and sends (a,b) to (1,0). Norm
surjectivity over the original quadratic finite field therefore clears the
second entry of any pair whose norm sum is nonzero. No nonzero norm sum is
assumed for arbitrary pairs of coordinates.

These rotations provide the local elimination step for `UnitVectorReduction`
in `Generation.Reduction`. They do not yet prove that an arbitrary norm-one
vector can be reduced by a sequence of such embedded rotations.

Source: Huppert II.10.4 (norm surjectivity); application to Aschbacher–Smith,
A.2.17, printed pp.38–39 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.OddFundamental.Generation
variable {F : Type*} [Field F] (σ : F ≃+* F) (hσ : Function.Involutive σ)

def planeMatrix (a b : F) : Matrix (Fin 2) (Fin 2) F := !![σ a, σ b; -b, a]

theorem planeMatrix_unitary (a b : F) (h : σ a * a + σ b * b = 1) :
    (form σ hσ 2).conjTranspose (planeMatrix σ a b) * planeMatrix σ a b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeMatrix, HermitianForm.conjTranspose, form, Matrix.mul_apply,
      Fin.sum_univ_two, hσ a, hσ b]
  · linear_combination h
  · ring
  · ring
  · linear_combination h

theorem planeMatrix_det (a b : F) (h : σ a * a + σ b * b = 1) :
    (planeMatrix σ a b).det = 1 := by
  simpa [planeMatrix, Matrix.det_fin_two] using h

def planeRotation (a b : F) (h : σ a * a + σ b * b = 1) :
    (form σ hσ 2).specialSubgroup :=
  let hu := planeMatrix_unitary σ hσ a b h
  ⟨⟨planeMatrix σ a b, (form σ hσ 2).conjTranspose (planeMatrix σ a b),
      mul_eq_one_comm.mp hu, hu⟩, by
    rw [HermitianForm.mem_specialSubgroup_iff]
    exact ⟨by simpa [form] using hu, Units.ext (planeMatrix_det σ a b h)⟩⟩

theorem planeRotation_mulVec (a b : F) (h : σ a * a + σ b * b = 1) :
    (planeRotation σ hσ a b h).val.val *ᵥ ![a, b] = ![1, 0] := by
  ext i
  fin_cases i <;> simp [planeRotation, planeMatrix, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]
  · exact h
  · ring

theorem exists_planeRotation_of_norm_sum_ne_zero [Finite F] {r e : ℕ} [Fact r.Prime]
    (he : 0 < e) (hc : Nat.card F = (r ^ e) ^ 2)
    (hj : ∀ x, σ x = x ^ (r ^ e)) (a b : F)
    (hab : σ a * a + σ b * b ≠ 0) :
    ∃ (c : F) (u : (form σ hσ 2).specialSubgroup), c ≠ 0 ∧
      σ c * c = σ a * a + σ b * b ∧ u.val.val *ᵥ ![a, b] = ![c, 0] := by
  have hq : IsPrimePow (r ^ e) := (isPrimePow_nat_iff _).mpr
    ⟨r, e, Fact.out, he, rfl⟩
  have hk := (form σ hσ 2).fixed_card_prime_power hq hc hj
  have hfix : σ (σ a * a + σ b * b) = σ a * a + σ b * b := by
    simp only [map_add, map_mul, hσ a, hσ b]
    ring
  obtain ⟨c, hc0, hcn⟩ := BenderSuzuki.External.huppert_II_10_4_norm_surjective
    (form σ hσ 2) (r ^ e) hc hk (σ a * a + σ b * b) hfix hab
  have hcn' : σ c * c = σ a * a + σ b * b := by
    simpa [form, mul_comm] using hcn
  have hnorm : σ (a/c) * (a/c) + σ (b/c) * (b/c) = 1 := by
    rw [map_div₀, map_div₀, div_mul_div_comm, div_mul_div_comm,
      ← add_div, ← hcn', div_self (mul_ne_zero ((map_ne_zero σ).mpr hc0) hc0)]
  refine ⟨c, planeRotation σ hσ (a/c) (b/c) hnorm, hc0, hcn', ?_⟩
  have hh := congrArg (fun x : Fin 2 → F => c • x)
    (planeRotation_mulVec σ hσ (a/c) (b/c) hnorm)
  rw [← Matrix.mulVec_smul] at hh
  have hin : c • ![a/c, b/c] = ![a,b] := by
    ext i
    fin_cases i <;> simp [smul_eq_mul, mul_div_cancel₀, hc0]
  rw [hin] at hh
  simpa [smul_eq_mul] using hh

end Theory.SpecificGroups.ClassicalUnitary.OddFundamental.Generation
