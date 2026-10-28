module

public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.FixedLine.TensorEmbedding
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.FixedLine.FlagInterpolation

/-!
# Transpose pairings and cyclic highest tensors for binary SL₃

The coordinate dot products on the natural and dual spaces, and the entrywise
matrix pairing on the trace-zero adjoint space, tensor to a pairing on the
actual `WordSpace`. Evaluating `wordPolynomial` at an upper-unitriangular
matrix equals pairing with the seed moved by its transpose. The recursive
squared-variable substitution matches the Frobenius twist in `wordRep`.

For a word of length `n` and a field of order `2^n`, polynomial injectivity
and finite-grid interpolation make this pairing nondegenerate. Finite
dimensionality then identifies every functional with a pairing vector.
A functional annihilating the lower-unitriangular seed orbit is zero, so
that orbit, and hence the full SL₃ orbit, spans the word. This includes
adjoint factors and `q = 2`, with no irreducibility or algebraic-closure premise.

Source: GLS III, 2.8.6(a), 2.8.9 and 2.8.10(c),
`refs/KGroup/GLS3/chapter2.tex`. These concrete coordinate arguments supply
the cyclic-vector input to tensor simplicity without invoking Curtis's
irreducibility hypothesis or the tensor-simplicity assembly.
-/

public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct MatrixGroups
open Matrix MvPolynomial Matrix.PSL3Even.UnipotentGeometry
namespace Representation.SL3.BinaryDefiningFactors.TensorSimplicity.FixedLine
variable (K : Type*) [Field K]

/-- Coordinate pairing on each of the four concrete restricted factors. -/
def factorPairing : (a : Factor) → Space K a →ₗ[K] Module.Dual K (Space K a)
  | .trivial => LinearMap.mul K K
  | .natural => ∑ i, (LinearMap.proj i).smulRight (LinearMap.proj i)
  | .dual => ∑ j, (dualEntry K j).smulRight (dualEntry K j)
  | .adjoint => ∑ i, ∑ j, (adjointEntry K i j).smulRight (adjointEntry K i j)

/-- Tensor product of the coordinate pairings on the actual word carrier. -/
def wordPairing : (w : List Factor) → WordSpace K w →ₗ[K] Module.Dual K (WordSpace K w)
  | [] => LinearMap.mul K K
  | a :: w => TensorProduct.dualDistrib K (Space K a) (WordSpace K w) ∘ₗ
      TensorProduct.map (factorPairing K a) (wordPairing w)

/-- The recursive pairing multiplies on pure tensors. -/
theorem wordPairing_tmul (a : Factor) (w : List Factor)
    (v v' : Space K a) (z z' : WordSpace K w) :
    wordPairing K (a :: w) (v ⊗ₜ[K] z) (v' ⊗ₜ[K] z') =
      factorPairing K a v v' * wordPairing K w z z' := by
  change TensorProduct.dualDistrib K _ _
    (TensorProduct.map _ _ (v ⊗ₜ[K] z)) (v' ⊗ₜ[K] z') = _
  rw [TensorProduct.map_tmul, TensorProduct.dualDistrib_apply]

variable {K} {F : Type*} [Field F] [CharP K 2]

omit [CharP K 2] in
private theorem transpose_inv (g : SL(3,F)) : g.transpose⁻¹ = (g⁻¹).transpose := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_inv, SpecialLinearGroup.coe_transpose,
    Matrix.adjugate_transpose]

omit [CharP K 2] in
private theorem natural_lower (ι : F →+* K) (u : U F) (v : Fin 3 → K) :
    natural ι (specialLinear F u).transpose v =
      ![v 0, ι u.x * v 0 + v 1, ι u.c * v 0 + ι u.y * v 1 + v 2] := by
  change (matrix F u).transpose.map ι *ᵥ v = _
  ext i
  fin_cases i <;> simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem natural_lower_inv (ι : F →+* K) (u : U F) (v : Fin 3 → K) :
    natural ι (specialLinear F u).transpose⁻¹ v =
      ![v 0, ι u.x * v 0 + v 1,
        (ι u.x * ι u.y + ι u.c) * v 0 + ι u.y * v 1 + v 2] := by
  rw [transpose_inv, ← map_inv, natural_lower]
  have hx : (u⁻¹).x = -u.x := rfl
  have hy : (u⁻¹).y = -u.y := rfl
  have hc : (u⁻¹).c = u.x * u.y - u.c := rfl
  simp [hx, hy, hc, CharTwo.neg_eq, sub_eq_add_neg]

/-- Polynomial evaluation is pairing with the transpose orbit of the factor seed. -/
theorem factorPolynomial_eval_pairing (ι : F →+* K) (a : Factor)
    (v : Space K a) (u : U F) :
    MvPolynomial.eval (point ι u) (factorPolynomial K a v) =
      factorPairing K a v
        (factorRep ι a (specialLinear F u).transpose (factorSeed K a)) := by
  cases a with
  | trivial =>
    change K at v
    change MvPolynomial.eval _ (C v) = v * 1
    simp
  | natural =>
    change (Fin 3 → K) at v
    change MvPolynomial.eval (point ι u) (∑ i : Fin 3, v i • leftRow K i) =
      ∑ i : Fin 3, v i •
      (natural ι (specialLinear F u).transpose (Pi.single 0 1)) i
    rw [natural_lower]
    simp [leftRow, point, Fin.sum_univ_three, mul_comm]
  | dual =>
    change Module.Dual K (Fin 3 → K) at v
    change _ = ∑ j : Fin 3, dualEntry K j v •
      (natural ι (specialLinear F u).transpose⁻¹ (Pi.single j 1)) 2
    simp [natural_lower_inv, factorPolynomial, rightColumn, point,
      Fin.sum_univ_three, dualEntry]
    ring
  | adjoint =>
    change AdjointSpace K at v
    change _ = ∑ i : Fin 3, ∑ j : Fin 3, adjointEntry K i j v •
      (natural ι (specialLinear F u).transpose
        ((natural ι (specialLinear F u).transpose⁻¹ (Pi.single j 1)) 2 • Pi.single 0 1)) i
    simp [map_smul, natural_lower, natural_lower_inv, factorPolynomial,
      leftRow, rightColumn, point, Fin.sum_univ_three, adjointEntry]
    ring

omit [CharP K 2] in
private theorem squareVariables_eval (x : Fin 3 → K) (p : Polynomial K) :
    MvPolynomial.eval x (squareVariables K p) =
      MvPolynomial.eval (fun i => x i ^ 2) p := by
  have h : (MvPolynomial.aeval x).comp (squareVariables K) =
      MvPolynomial.aeval (fun i => x i ^ 2) := by
    ext i
    simp [squareVariables]
  exact AlgHom.congr_fun h p

/-- Opposite-unitriangular seed orbits realize all polynomial evaluations. -/
theorem wordPolynomial_eval_pairing (ι : F →+* K) (w : List Factor)
    (v : WordSpace K w) (u : U F) :
    MvPolynomial.eval (point ι u) (wordPolynomial K w v) =
      wordPairing K w v
        (wordRep ι w (specialLinear F u).transpose (wordSeed K w)) := by
  induction w generalizing ι with
  | nil =>
    change K at v
    change MvPolynomial.eval _ (C v) = v * 1
    simp
  | cons a w ih =>
    induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | tmul v z =>
      change MvPolynomial.eval (point ι u) (wordPolynomial K (a :: w) (v ⊗ₜ[K] z)) =
        wordPairing K (a :: w) (v ⊗ₜ[K] z)
          (factorRep ι a (specialLinear F u).transpose (factorSeed K a) ⊗ₜ[K]
            wordRep ((frobenius K 2).comp ι) w (specialLinear F u).transpose (wordSeed K w))
      rw [wordPolynomial_tmul, wordPairing_tmul, map_mul, squareVariables_eval]
      have hp : (fun i => point ι u i ^ 2) = point ((frobenius K 2).comp ι) u := by
        ext i
        fin_cases i <;> simp [point, frobenius_def]
      rw [hp, factorPolynomial_eval_pairing, ih]
    | add v z hv hz => simp only [map_add, LinearMap.add_apply, hv, hz]

/-- The finite-field polynomial coefficients separate every source-restricted word. -/
theorem eq_zero_of_wordPolynomial_eval_eq_zero [Finite F] (ι : F →+* K)
    (n : ℕ) (hcard : Nat.card F = 2 ^ n) (w : List Factor) (hw : w.length = n)
    (v : WordSpace K w)
    (hv : ∀ u : U F, MvPolynomial.eval (point ι u) (wordPolynomial K w v) = 0) :
    v = 0 := by
  apply wordPolynomial_injective K w
  rw [map_zero]
  have hweight : (wordWeight w).1 < 2 ^ n ∧ (wordWeight w).2 < 2 ^ n := by
    simpa only [hw] using wordWeight_lt w
  exact eq_zero_of_flagSpace_eval_eq_zero ι n _ _ hcard hweight.1 hweight.2 _
    (wordPolynomial_mem_flagSpace K w v) hv

private theorem wordPairing_injective [Finite F] (ι : F →+* K)
    (n : ℕ) (hcard : Nat.card F = 2 ^ n) (w : List Factor) (hw : w.length = n) :
    Function.Injective (wordPairing K w) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply eq_zero_of_wordPolynomial_eval_eq_zero ι n hcard w hw v
  intro u
  rw [wordPolynomial_eval_pairing, hv]
  rfl

/-- The lower-unitriangular orbit of the highest tensor spans every restricted word. -/
theorem wordSeed_lower_orbit_span [Finite F] (ι : F →+* K)
    (n : ℕ) (hcard : Nat.card F = 2 ^ n) (w : List Factor) (hw : w.length = n) :
    Submodule.span K (Set.range fun u : U F =>
      wordRep ι w (specialLinear F u).transpose (wordSeed K w)) = ⊤ := by
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply bot_unique
  intro f hf
  have hs : Function.Surjective (wordPairing K w) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      Subspace.dual_finrank_eq.symm).mp (wordPairing_injective ι n hcard w hw)
  obtain ⟨v, rfl⟩ := hs f
  have hv : v = 0 := by
    apply eq_zero_of_wordPolynomial_eval_eq_zero ι n hcard w hw v
    intro u
    rw [wordPolynomial_eval_pairing]
    exact (Submodule.mem_dualAnnihilator _).mp hf _ (Submodule.subset_span ⟨u, rfl⟩)
  simp [hv]

end FixedLine
open FixedLine

/-- Every restricted tensor word is spanned by the SL₃ orbit of its highest tensor. -/
theorem wordSeed_orbit_span {F K : Type*} [Field F] [Field K] [CharP K 2] [Finite F]
    (ι : F →+* K) (n : ℕ) (hcard : Nat.card F = 2 ^ n)
    (w : List Factor) (hw : w.length = n) :
    Submodule.span K (Set.range fun g : SL(3,F) =>
      wordRep ι w g (wordSeed K w)) = ⊤ := by
  apply top_unique
  rw [← wordSeed_lower_orbit_span ι n hcard w hw]
  apply Submodule.span_mono
  rintro _ ⟨u, rfl⟩
  exact ⟨(specialLinear F u).transpose, rfl⟩

end Representation.SL3.BinaryDefiningFactors.TensorSimplicity
