module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Levi.Restriction
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Kernel and factorization of the unitary-five plane stabilizer

For the identity Hermitian form in characteristic two, the kernel of restriction
from the special-unitary plane stabilizer to GL₂ is exactly the existing group
of unipotent parameters. In the original `flagBasis`, pointwise fixation gives
the first two columns, unitarity gives the last two rows, and determinant one
forces the middle diagonal entry to be one. The remaining unitary equations
recover the conjugate row and the relation `z + z* = x x*`.

The Gram matrix used below retains the nonzero dual-plane diagonal block of
`flagBasis`. No trace-one scalar is needed for kernel exhaustion or normality.
Given the trace-one scalar used by the Levi section, every stabilizer element
factors as a parameter unipotent times its Levi restriction. The parameter image
is normal in this stabilizer, and its image is normal in the actual projective
plane parabolic by the surjectivity of the restricted projective map.

These are the kernel and factorization ingredients for the plane-parabolic
calculation in Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.12(7), printed pp.263--264. Identification of the two-core, the full quotient,
and the index-three residual is separate.
-/

public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.PlaneCore
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

private def kernelGram : Matrix (Fin 5) (Fin 5) F :=
  !![0,0,0,1,0; 0,0,0,0,1; 0,0,1,0,0; 1,0,0,1,0; 0,1,0,0,1]

private theorem kernelGram_eq :
    kernelGram = J.conjTranspose (flagBasis (F := F)) * flagBasis := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kernelGram, flagBasis, HermitianForm.conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

private theorem kernel_normal_form (N : Matrix (Fin 5) (Fin 5) F)
    (hc0 : ∀ i, N i 0 = (1 : Matrix (Fin 5) (Fin 5) F) i 0)
    (hc1 : ∀ i, N i 1 = (1 : Matrix (Fin 5) (Fin 5) F) i 1)
    (hu : J.conjTranspose N * kernelGram * N = kernelGram)
    (hd : N.det = 1) : ∃ u : Parameters J, N = u.matrix := by
  have hr3 (j : Fin 5) : N 3 j = kernelGram (F := F) 0 j := by
    have h := congrArg (fun A : Matrix (Fin 5) (Fin 5) F => A 0 j) hu
    simpa [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ,
      hc0, kernelGram] using h
  have hr4 (j : Fin 5) : N 4 j = kernelGram (F := F) 1 j := by
    have h := congrArg (fun A : Matrix (Fin 5) (Fin 5) F => A 1 j) hu
    simpa [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ,
      hc1, kernelGram, Matrix.one_apply] using h
  have ht : N.IsUpperTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [kernelGram]
  have hm : N 2 2 = 1 := by
    rw [Matrix.det_of_isUpperTriangular ht] at hd
    simpa [Fin.prod_univ_succ, hc0, hc1, hr3, hr4, kernelGram] using hd
  have hn : N =
      !![1,0,N 0 2,N 0 3,N 0 4;
         0,1,N 1 2,N 1 3,N 1 4;
         0,0,1,N 2 3,N 2 4;
         0,0,0,1,0;
         0,0,0,0,1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc0, hc1, hr3, hr4, hm, kernelGram]
  have h23 : N 2 3 = J.conj (N 0 2) := by
    have h := congrArg (fun A : Matrix (Fin 5) (Fin 5) F => A 2 3) hu
    conv at h => lhs; rw [hn]
    simpa [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ,
      kernelGram, CharTwo.add_eq_zero] using h
  have h24 : N 2 4 = J.conj (N 1 2) := by
    have h := congrArg (fun A : Matrix (Fin 5) (Fin 5) F => A 2 4) hu
    conv at h => lhs; rw [hn]
    simpa [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ,
      kernelGram, CharTwo.add_eq_zero] using h
  let x : Fin 2 → F := ![N 0 2, N 1 2]
  let z : Matrix (Fin 2) (Fin 2) F := !![N 0 3,N 0 4;N 1 3,N 1 4]
  have hz : ∀ i j, z i j + J.conj (z j i) = x i * J.conj (x j) := by
    intro i j
    have h := congrArg (fun A : Matrix (Fin 5) (Fin 5) F =>
      A (if i = 0 then 3 else 4) (if j = 0 then 3 else 4)) hu
    conv at h => lhs; rw [hn]
    fin_cases i <;> fin_cases j <;>
      simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ,
        kernelGram, h23, h24, Parameters.conj_conj] at h
    all_goals
      simp [x, z]
      apply CharTwo.add_eq_zero.mp
      linear_combination h
  refine ⟨⟨x, z, hz⟩, ?_⟩
  conv => lhs; rw [hn]
  simp [Parameters.matrix, x, z, h23, h24]

omit [CharP F 2] in
private theorem kernel_ct_mul (A B : Matrix (Fin 5) (Fin 5) F) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((A * B).map J.conj).transpose =
    (B.map J.conj).transpose * (A.map J.conj).transpose
  rw [Matrix.map_mul, Matrix.transpose_mul]

set_option maxRecDepth 2048 in
/-- Every special-unitary pointwise plane fixer is one of the explicit unipotents. -/
theorem exists_parameters_of_fixes_plane (hJ : J.form = 1)
    (g : J.specialSubgroup)
    (hg : ∀ v : plane F, linearAction J g v.val = v.val) :
    ∃ u : Parameters J, Parameters.toSU hJ u = g := by
  let P : Matrix (Fin 5) (Fin 5) F := flagBasis
  let Pi : Matrix (Fin 5) (Fin 5) F := flagBasisInv
  let N : Matrix (Fin 5) (Fin 5) F := Pi * g.val.val * P
  have hPPi : P * Pi = 1 := flagBasis_mul_inv
  have hPiP : Pi * P = 1 := flagBasis_inv_mul
  have hgram : kernelGram = J.conjTranspose P * P := kernelGram_eq J
  have hstar : J.conjTranspose Pi * J.conjTranspose P = 1 := by
    rw [← kernel_ct_mul, hPPi]
    change ((J.conj : F →+* F).mapMatrix 1).transpose = 1
    rw [map_one, Matrix.transpose_one]
  have hgU := ((J.mem_specialSubgroup_iff g.val).mp g.property).1
  rw [hJ, mul_one] at hgU
  have hu : J.conjTranspose N * kernelGram * N = kernelGram := by
    change J.conjTranspose (Pi * g.val.val * P) * kernelGram *
      (Pi * g.val.val * P) = kernelGram
    rw [kernel_ct_mul, kernel_ct_mul, hgram]
    calc
      J.conjTranspose P * (J.conjTranspose g.val.val * J.conjTranspose Pi) *
          (J.conjTranspose P * P) * (Pi * g.val.val * P) =
        J.conjTranspose P * J.conjTranspose g.val.val *
          (J.conjTranspose Pi * J.conjTranspose P) * (P * Pi) * g.val.val * P := by
            simp only [mul_assoc]
      _ = J.conjTranspose P * (J.conjTranspose g.val.val * g.val.val) * P := by
        rw [hstar, hPPi]
        simp only [mul_one, mul_assoc]
      _ = J.conjTranspose P * P := by rw [hgU, mul_one]
  have hdg : g.val.val.det = 1 :=
    congrArg Units.val (((J.mem_specialSubgroup_iff g.val).mp g.property).2)
  have hd : N.det = 1 := by
    change (Pi * g.val.val * P).det = 1
    rw [Matrix.det_mul, Matrix.det_mul, hdg, mul_one, ← Matrix.det_mul, hPiP,
      Matrix.det_one]
  have hcol (q : Fin 5) (hq : q = 0 ∨ q = 1) (i : Fin 5) :
      N i q = (1 : Matrix (Fin 5) (Fin 5) F) i q := by
    have hmem : (fun k => P k q) ∈ plane F := by
      rcases hq with rfl | rfl <;> simp [P, flagBasis, plane]
    have hfix : g.val.val *ᵥ (fun k => P k q) = (fun k => P k q) := hg ⟨_, hmem⟩
    calc
      N i q = (Pi *ᵥ (g.val.val *ᵥ (fun k => P k q))) i := by
        simp [N, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      _ = (Pi * P) i q := by rw [hfix]; rfl
      _ = (1 : Matrix (Fin 5) (Fin 5) F) i q := by rw [hPiP]
  obtain ⟨u, hu⟩ := kernel_normal_form J N
    (hcol 0 (Or.inl rfl)) (hcol 1 (Or.inr rfl)) hu hd
  refine ⟨u, ?_⟩
  apply Subtype.ext
  apply Units.ext
  change (Parameters.ambientGL u).val = g.val.val
  rw [Parameters.ambientGL_val, Parameters.ambientMatrix_eq, ← hu]
  change P * (Pi * g.val.val * P) * Pi = g.val.val
  calc
    P * (Pi * g.val.val * P) * Pi = (P * Pi) * g.val.val * (P * Pi) := by
      simp only [mul_assoc]
    _ = g.val.val := by rw [hPPi]; simp

/-- The explicit parameter group exhausts the kernel of plane restriction. -/
theorem ker_planeRestriction (hJ : J.form = 1) :
    (planeRestriction J).ker = (Parameters.toStabilizer hJ).range := by
  apply le_antisymm
  · intro g hg
    have hfix := (planeRestriction_eq_one_iff J g).mp hg
    obtain ⟨u, hu⟩ := exists_parameters_of_fixes_plane J hJ g.val hfix
    exact ⟨u, Subtype.ext hu⟩
  · exact parameters_le_ker_restriction J hJ

/-- Normality inside the special-unitary plane stabilizer. -/
theorem parameters_range_normal (hJ : J.form = 1) :
    (Parameters.toStabilizer hJ).range.Normal := by
  rw [← ker_planeRestriction J hJ]
  infer_instance

/-- Every special-unitary plane stabilizer element is a unipotent times the
Levi section of its restriction. -/
theorem planeStabilizer_factorization (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) (g : specialStabilizer J (plane F)) :
    ∃ u : Parameters J, g = Parameters.toStabilizer hJ u *
      planeLeviStabilizer J c hc hJ (planeRestriction J g) := by
  let l := planeLeviStabilizer J c hc hJ (planeRestriction J g)
  have hk : g * l⁻¹ ∈ (planeRestriction J).ker := by
    change planeRestriction J (g * l⁻¹) = 1
    simp [l]
  rw [ker_planeRestriction J hJ] at hk
  obtain ⟨u, hu⟩ := hk
  exact ⟨u, by rw [hu]; simp [l]⟩

/-- The explicit projective unipotents are normal in the actual plane parabolic. -/
theorem projectiveUnipotent_normal (hJ : J.form = 1) :
    (projectiveUnipotent J hJ).Normal := by
  change (((project J).subgroupMap (specialStabilizer J (plane F))).comp
    (Parameters.toStabilizer hJ)).range.Normal
  rw [MonoidHom.range_comp]
  exact (parameters_range_normal J hJ).map _
    ((project J).subgroupMap_surjective (specialStabilizer J (plane F)))

/-- The same factorization after the actual surjective projective map. -/
theorem planeParabolic_factorization (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) (g : planeParabolic J) :
    ∃ (u : Parameters J) (A : GL (Fin 2) F),
      g = Parameters.toParabolic hJ u * planeLeviParabolic J c hc hJ A := by
  obtain ⟨s, rfl⟩ :=
    (project J).subgroupMap_surjective (specialStabilizer J (plane F)) g
  obtain ⟨u, hu⟩ := planeStabilizer_factorization J c hc hJ s
  refine ⟨u, planeRestriction J s, ?_⟩
  exact congrArg ((project J).subgroupMap (specialStabilizer J (plane F))) hu

end Theory.SpecificGroups.UnitaryFive.PlaneCore
