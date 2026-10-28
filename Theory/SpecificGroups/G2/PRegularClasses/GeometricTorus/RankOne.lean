module

public import Theory.LinearAlgebra.TwoDimensionalSemisimple
public import Theory.SpecificGroups.G2.PRegularClasses.GeometricTorus.Reduction

/-!
# Diagonalizing the opposite-pair stabilizer inside G₂

An octonion automorphism scaling the zeroth and seventh coordinate vectors
factors as a torus element times the checked SL₂ pair stabilizer. Its action
on the plane spanned by the fifth and sixth coordinate vectors therefore
has a literal two-dimensional matrix. For odd-order elements in
characteristic two this action is semisimple. A determinant-one eigenbasis
lifts through the SL₂ embedding to an octonion automorphism. The product
of the two remaining eigenvalues is forced by octonion multiplication,
identifying the conjugate with the specified two-parameter torus element.

This is the final block calculation in the direct G₂ proof of the
semisimple-torus geometry in GLS III, 1.4.2(e) and 1.4.3(b)
(`refs/KGroup/GLS3/Chapter1.tex`). The explicit SL₂ embedding is from the
licensed ATLAS port; see `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`.
-/

public section

open Atlas.SplitOctonion Matrix
open scoped MatrixGroups
namespace Atlas.G2.PRegularClasses
variable {K : Type*} [Field K]

private def plane (v : Fin 2 → K) : Carrier K := ![0,0,0,0,0,v 0,v 1,0]

private theorem plane_injective : Function.Injective (plane (K := K)) := by
  intro v w h
  ext i
  fin_cases i
  · exact congrFun h 5
  · exact congrFun h 6

private theorem plane_smul (r : K) (v : Fin 2 → K) :
    plane (r • v) = r • plane v := by
  ext i
  fin_cases i <;> simp [plane]

private theorem blockHom_plane (M : SL(2,K)) (v : Fin 2 → K) :
    (PairStabilizer.blockHom M).val (plane v) = plane (M.val *ᵥ v) := by
  ext i
  fin_cases i <;> simp [PairStabilizer.blockHom, PairStabilizer.blockEquiv,
    PairStabilizer.blockLinear, plane, mulVec, dotProduct, Fin.sum_univ_two]

private theorem blockHom_basis_five (Q : SL(2,K)) :
    (PairStabilizer.blockHom Q).val (basisVector 5) = plane ![Q.val 0 0, Q.val 1 0] := by
  ext i
  fin_cases i <;> simp [PairStabilizer.blockHom, PairStabilizer.blockEquiv,
    PairStabilizer.blockLinear, plane, basisVector]

private theorem blockHom_basis_six (Q : SL(2,K)) :
    (PairStabilizer.blockHom Q).val (basisVector 6) = plane ![Q.val 0 1, Q.val 1 1] := by
  ext i
  fin_cases i <;> simp [PairStabilizer.blockHom, PairStabilizer.blockEquiv,
    PairStabilizer.blockLinear, plane, basisVector]

private theorem torus_basis (a b : Kˣ) (i : Fin 8) :
    (torus a b).val (basisVector i) = (torusWeights a b i : K) • basisVector i := by
  ext j
  by_cases h : i = j
  · subst j
    simp [torus, torusEquiv, torusLinear, basisVector]
  · simp [torus, torusEquiv, torusLinear, basisVector, Ne.symm h]

private theorem basis_five_mul_six :
    mul (basisVector 5 : Carrier K) (basisVector 6) = basisVector 7 := by
  ext i; fin_cases i <;> simp [mul, basisVector]

private theorem scaling_pair_factor (g : Model K) (a : Kˣ)
    (h0 : g.val (basisVector 0) = (a : K) • basisVector 0)
    (h7 : g.val (basisVector 7) = (↑a⁻¹ : K) • basisVector 7) :
    ∃ M : SL(2,K), g = torus a 1 * PairStabilizer.blockHom M := by
  let p : PairStabilizer.fixingPair (F := K) := ⟨(torus a 1)⁻¹ * g, by
    constructor
    · change (torus a 1).val.symm (g.val (basisVector 0)) = basisVector 0
      apply (torus a 1).val.injective
      rw [LinearEquiv.apply_symm_apply, h0]
      ext i
      fin_cases i <;> simp [torus, torusEquiv, torusLinear, torusWeights, basisVector]
    · change (torus a 1).val.symm (g.val (basisVector 7)) = basisVector 7
      apply (torus a 1).val.injective
      rw [LinearEquiv.apply_symm_apply, h7]
      ext i
      fin_cases i <;> simp [torus, torusEquiv, torusLinear, torusWeights, basisVector]⟩
  refine ⟨PairStabilizer.imageSL p, ?_⟩
  have he := congrArg Subtype.val (PairStabilizer.block_imageSL p)
  change PairStabilizer.blockHom (PairStabilizer.imageSL p) = (torus a 1)⁻¹ * g at he
  rw [he, mul_inv_cancel_left]

private theorem exists_plane_matrix (g : Model K) (a : Kˣ)
    (h0 : g.val (basisVector 0) = (a : K) • basisVector 0)
    (h7 : g.val (basisVector 7) = (↑a⁻¹ : K) • basisVector 7) :
    ∃ A : Matrix (Fin 2) (Fin 2) K, ∀ v, g.val (plane v) = plane (A *ᵥ v) := by
  obtain ⟨M, rfl⟩ := scaling_pair_factor g a h0 h7
  refine ⟨!![(↑a⁻¹ : K) * M.val 0 0, (↑a⁻¹ : K) * M.val 0 1;
    M.val 1 0, M.val 1 1], ?_⟩
  intro v
  change (torus a 1).val ((PairStabilizer.blockHom M).val (plane v)) = _
  rw [blockHom_plane]
  ext i
  fin_cases i <;>
    simp [plane, torus, torusEquiv, torusLinear, torusWeights,
      mulVec, dotProduct, Fin.sum_univ_two, _root_.mul_add, mul_assoc]

private theorem plane_action_semisimple [CharP K 2]
    (g : Model K) (hg : ¬ 2 ∣ orderOf g) (f : Module.End K (Fin 2 → K))
    (hf : ∀ v, g.val (plane v) = plane (f v)) : f.IsSemisimple := by
  have hp (n : ℕ) (v : Fin 2 → K) : (action g ^ n) (plane v) = plane ((f ^ n) v) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply, ih]
      exact hf _
  have hp' : f ^ orderOf g = 1 := by
    apply LinearMap.ext
    intro v
    have he := hp (orderOf g) v
    rw [action_pow_orderOf] at he
    exact (plane_injective he).symm
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.separable_X_pow_sub_C' 2 (orderOf g) (1 : K) hg one_ne_zero).squarefree
  simp [hp']

/-- Three indicated singular vectors generate the octonion algebra. -/
private theorem ext_on_basis_zero_five_six (g h : Model K)
    (h0 : g.val (basisVector 0) = h.val (basisVector 0))
    (h5 : g.val (basisVector 5) = h.val (basisVector 5))
    (h6 : g.val (basisVector 6) = h.val (basisVector 6)) : g = h := by
  have hp (u v : Carrier K) (hu : g.val u = h.val u) (hv : g.val v = h.val v) :
      g.val (mul u v) = h.val (mul u v) := by
    rw [automorphism_mul, automorphism_mul, hu, hv]
  have e56 := basis_five_mul_six (K := K)
  have e05 : mul (basisVector 0 : Carrier K) (basisVector 5) = basisVector 1 := by
    ext i; fin_cases i <;> simp [mul, basisVector]
  have e06 : mul (basisVector 0 : Carrier K) (basisVector 6) = -basisVector 2 := by
    ext i; fin_cases i <;> simp [mul, basisVector]
  have e07 : mul (basisVector 0 : Carrier K) (basisVector 7) = -basisVector 3 := by
    ext i; fin_cases i <;> simp [mul, basisVector]
  have e70 : mul (basisVector 7 : Carrier K) (basisVector 0) = -basisVector 4 := by
    ext i; fin_cases i <;> simp [mul, basisVector]
  have h7 := hp _ _ h5 h6
  rw [e56] at h7
  have h1 := hp _ _ h0 h5
  rw [e05] at h1
  have h2 := hp _ _ h0 h6
  rw [e06, map_neg, map_neg, neg_inj] at h2
  have h3 := hp _ _ h0 h7
  rw [e07, map_neg, map_neg, neg_inj] at h3
  have h4 := hp _ _ h7 h0
  rw [e70, map_neg, map_neg, neg_inj] at h4
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun K (Fin 8)).ext
  intro i
  change g.val ((Pi.basisFun K (Fin 8)) i) = h.val ((Pi.basisFun K (Fin 8)) i)
  simp only [Pi.basisFun_apply]
  change g.val (basisVector i) = h.val (basisVector i)
  fin_cases i <;> assumption

/-- The subgroup scaling an opposite singular pair has the required torus
normal form for odd-order elements. -/
theorem isConj_torus_of_scaling_pair [IsAlgClosed K] [CharP K 2]
    (g : Model K) (hg : ¬ 2 ∣ orderOf g) (a : Kˣ)
    (h0 : g.val (basisVector 0) = (a : K) • basisVector 0)
    (h7 : g.val (basisVector 7) = (↑a⁻¹ : K) • basisVector 7) :
    ∃ m : Kˣ, IsConj g (torus a m) := by
  obtain ⟨A, hA⟩ := exists_plane_matrix g a h0 h7
  let f := Matrix.toLin' A
  have hf : ∀ v, g.val (plane v) = plane (f v) := hA
  obtain ⟨Q, μ, ν, hμ, hν⟩ := Module.End.exists_specialLinear_eigenbasis_fin_two f
    (plane_action_semisimple g hg f hf)
  let b := PairStabilizer.blockHom Q
  let d := b⁻¹ * g * b
  have hb0 : b.val (basisVector 0) = basisVector 0 :=
    (PairStabilizer.block_mem_fixingPair Q).1
  have hb7 : b.val (basisVector 7) = basisVector 7 :=
    (PairStabilizer.block_mem_fixingPair Q).2
  have hb5 : b.val (basisVector 5) = plane ![Q.val 0 0, Q.val 1 0] := blockHom_basis_five Q
  have hb6 : b.val (basisVector 6) = plane ![Q.val 0 1, Q.val 1 1] := blockHom_basis_six Q
  have hd0 : d.val (basisVector 0) = (a : K) • basisVector 0 := by
    apply b.val.injective
    change b.val (b.val.symm (g.val (b.val (basisVector 0)))) = _
    rw [LinearEquiv.apply_symm_apply, hb0, h0, map_smul, hb0]
  have hd7 : d.val (basisVector 7) = (↑a⁻¹ : K) • basisVector 7 := by
    apply b.val.injective
    change b.val (b.val.symm (g.val (b.val (basisVector 7)))) = _
    rw [LinearEquiv.apply_symm_apply, hb7, h7, map_smul, hb7]
  have hd5 : d.val (basisVector 5) = μ • basisVector 5 := by
    apply b.val.injective
    change b.val (b.val.symm (g.val (b.val (basisVector 5)))) = _
    rw [LinearEquiv.apply_symm_apply, map_smul, hb5, hf, hμ, plane_smul]
  have hd6 : d.val (basisVector 6) = ν • basisVector 6 := by
    apply b.val.injective
    change b.val (b.val.symm (g.val (b.val (basisVector 6)))) = _
    rw [LinearEquiv.apply_symm_apply, map_smul, hb6, hf, hν, plane_smul]
  have hν0 : ν ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hd6
    have he := d.val.injective (hd6.trans (map_zero _).symm)
    have hh := congrFun he 6
    simp [basisVector] at hh
  have e56 := basis_five_mul_six (K := K)
  have hprod : μ * ν = (↑a⁻¹ : K) := by
    have he := automorphism_mul d (basisVector 5) (basisVector 6)
    rw [e56, hd7, hd5, hd6, SplitOctonion.smul_mul, SplitOctonion.mul_smul, e56, smul_smul] at he
    simpa [basisVector] using (congrFun he 7).symm
  let m := (Units.mk0 ν hν0)⁻¹
  have hμ' : μ = (↑a⁻¹ : K) * (m : K) := by
    change μ = (↑a⁻¹ : K) * ν⁻¹
    rw [← hprod, mul_assoc, mul_inv_cancel₀ hν0, mul_one]
  have hd : d = torus a m := by
    apply ext_on_basis_zero_five_six
    · rw [hd0, torus_basis]
      rfl
    · rw [hd5, hμ', torus_basis]
      rfl
    · rw [hd6, torus_basis]
      change ν • basisVector 6 = (↑m⁻¹ : K) • basisVector 6
      simp only [m, inv_inv, Units.val_mk0]
  refine ⟨m, isConj_iff.mpr ⟨b⁻¹, ?_⟩⟩
  simpa only [inv_inv] using hd

end Atlas.G2.PRegularClasses
