module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Parabolic.Blocks.Exhaustion.FixedVector
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourScalarKernel

/-!
# Exhaustion of the projective unitary-five line stabilizer over F₁₆

Lift a projective parabolic element to the actual SU₅ line stabilizer. Its
nonzero line eigenvalue `a` splits as `a⁶ (a⁵)²`, where `a⁶` is a fifth root
and `a⁵` is a cubic root. Removing the corresponding scalar and cubic matrices
fixes the marked vector, so the vector-stabilizer factorization applies. The
fifth-root scalar has trivial projective image. The resulting radical, SU₃,
and cubic factors all belong to the established full-product map's image.

Source: the classical parabolic calculation supporting Aschbacher--Smith,
*The Classification of Quasithin Groups*, F.1.11--12(7), printed pp.262--264.
-/

@[expose] public section
open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic.Blocks.Exhaustion
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

omit [CharP F 2] in
/-- A line stabilizer acts on the chosen nonzero vector by a nonzero scalar. -/
theorem line_eigenvalue (g : J.specialSubgroup) (hg : g ∈ specialStabilizer J (line F)) :
    ∃ a : F, a ≠ 0 ∧ linearAction J g lineVector = a • lineVector := by
  have hv : linearAction J g lineVector ∈ line F :=
    ((mem_specialStabilizer_iff J (line F) g).mp hg lineVector).mpr (by simp [lineVector, line])
  let a : F := (linearAction J g lineVector) 0
  have he : linearAction J g lineVector = a • lineVector := by
    change (linearAction J g lineVector) 1 = (linearAction J g lineVector) 0 ∧
      (linearAction J g lineVector) 2 = 0 ∧ (linearAction J g lineVector) 3 = 0 ∧
      (linearAction J g lineVector) 4 = 0 at hv
    ext i
    fin_cases i
    · simp [lineVector, a]
    · simpa [lineVector, a] using hv.1
    · simpa [lineVector] using hv.2.1
    · simpa [lineVector] using hv.2.2.1
    · simpa [lineVector] using hv.2.2.2
  refine ⟨a, ?_, he⟩
  intro ha
  have hz : lineVector (F := F) = 0 := (linearAction J g).injective (by simpa [ha] using he)
  have hh := congrFun hz 0
  simp [lineVector] at hh

omit [CharP F 2] in
/-- Split a nonzero F₁₆ scalar into its fifth-root and cubic factors. -/
theorem scalar_factors [Finite F] (hcard : Nat.card F = 16) (a : F) (ha : a ≠ 0) :
    ∃ (l : rootsOfUnity 5 F) (b : Cubic (F := F)),
      (l.val : F) * (b.val : F)^2 = a := by
  let : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = 16 := (Nat.card_eq_fintype_card).symm.trans hcard
  have hp : a^15 = 1 := by simpa [hc] using FiniteField.pow_card_sub_one_eq_one a ha
  let b : Cubic (F := F) := ⟨Units.mk0 (a^5) (pow_ne_zero _ ha), by
    apply (mem_rootsOfUnity' 3 _).mpr
    change (a^5)^3 = 1
    simpa only [← pow_mul] using hp⟩
  let l : rootsOfUnity 5 F := ⟨Units.mk0 (a^6) (pow_ne_zero _ ha), by
    apply (mem_rootsOfUnity' 5 _).mpr
    change (a^6)^5 = 1
    rw [← pow_mul, show 6 * 5 = 15 * 2 from rfl, pow_mul, hp, one_pow]⟩
  refine ⟨l, b, ?_⟩
  change a^6 * (a^5)^2 = a
  rw [← pow_mul, ← pow_add, show 6 + 5 * 2 = 15 + 1 from rfl, pow_succ, hp, one_mul]

set_option maxRecDepth 2048 in
/-- Every actual projective line stabilizer is represented by the full block product. -/
theorem fullMap_surjective [Finite F] (hconj : ∀ x, J.conj x = x^4)
    (hcard : Nat.card F = 16) (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    Function.Surjective (fullMap J hconj c hc hJ) := by
  intro p
  obtain ⟨g, hg, hgp⟩ := p.property
  obtain ⟨a, ha, he⟩ := line_eigenvalue J g hg
  obtain ⟨l, b, hlb⟩ := scalar_factors hcard a ha
  let S : J.specialSubgroup := (scalarToKernel J hconj l).val
  let T : J.specialSubgroup := cubicSU J hconj c hc hJ b
  have hS (v : Fin 5 → F) : linearAction J S v = (l.val : F) • v := by
    change (GeneralLinearGroup.scalar (Fin 5) l.val).val *ᵥ v = _
    ext i
    simp [GeneralLinearGroup.coe_scalar, Matrix.scalar, mulVec_diagonal]
  have hT : linearAction J T lineVector = (b.val : F)^2 • lineVector := by
    change (cubicGL c b).val *ᵥ lineVector = _
    rw [cubicGL_matrix]
    ext i
    fin_cases i <;> simp [lineVector, cubicAmbientMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] <;> ring_nf <;> simp [CharTwo.two_eq_zero]
  have hST : linearAction J (S * T) lineVector = linearAction J g lineVector := by
    rw [map_mul, LinearEquiv.mul_apply, hS, hT, smul_smul, hlb, he]
  let H : J.specialSubgroup := (S * T)⁻¹ * g
  have hH : linearAction J H lineVector = lineVector := by
    change linearAction J ((S * T)⁻¹ * g) lineVector = _
    rw [map_mul, map_inv]
    change (linearAction J (S * T)).symm (linearAction J g lineVector) = lineVector
    rw [← hST]
    exact (linearAction J (S * T)).symm_apply_apply lineVector
  obtain ⟨u, A, hUA⟩ := fixed_lineVector_decomposition J c hc hJ H hH
  have hgfact : g = S * (T * (toSU J hJ u * leviSU J hJ A)) := by
    rw [← hUA]
    dsimp [H]
    group
  have hSp : project J S = 1 := (scalarToKernel J hconj l).property
  have hp : project J g =
      project J T * (project J (toSU J hJ u) * project J (leviSU J hJ A)) := by
    rw [hgfact, map_mul, map_mul, map_mul, hSp, one_mul]
  refine ⟨SemidirectProduct.inr (1, b) *
    (SemidirectProduct.inl u * SemidirectProduct.inr (A, 1)), ?_⟩
  apply Subtype.ext
  rw [map_mul, map_mul]
  change (toParabolic J hJ 1 * (leviParabolic J hJ 1 * cubicParabolic J hconj c hc hJ b)).val *
    ((toParabolic J hJ u * (leviParabolic J hJ 1 * cubicParabolic J hconj c hc hJ 1)).val *
      (toParabolic J hJ 1 * (leviParabolic J hJ A * cubicParabolic J hconj c hc hJ 1)).val) = p.val
  simp only [map_one, one_mul, mul_one]
  change project J T * (project J (toSU J hJ u) * project J (leviSU J hJ A)) = p.val
  exact hp.symm.trans hgp

end Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic.Blocks.Exhaustion
