module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Descent.SymmetricSimilarity
import all Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Descent.SymmetricSimilarity

/-!
# Fixed symmetric ternary similarity for every odd prime

Discriminant classification over the actual fixed field makes every
nondegenerate symmetric ternary form similar to the antidiagonal form.
The fixed-field characteristic need only be odd, including three.

This extends the proof in
`OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Descent.SymmetricSimilarity`
without changing its existing congruence-restricted interface. The internal
import deliberately reuses its private matrix comparison in this proof split,
preserving the existing public boundary.
The finite-form classification and its attribution remain in the imported
`SymmetricSimilarity.FiniteForms` module.
Source: GLS3, §§2.7 and 4.3; Aschbacher–Smith E.6.18, printed p.252.
-/

open Matrix
noncomputable section
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddInvolutionNormalization
open OddPrimeSylow.NormalizedOuter.Descent

/-- A nonsingular fixed symmetric ternary matrix is congruent, over the fixed
field, to a nonzero fixed scalar multiple of the prescribed Hermitian matrix.
The scalar accounts for the two possible discriminant square classes. -/
public theorem fixed_symmetric_ternary_similarity
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (_hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (S : Matrix (Fin 3) (Fin 3) E)
    (hs : S.transpose = S) (hfix : S.map J.conj = S) (hd : S.det ≠ 0) :
    ∃ (a : E) (C : GL (Fin 3) E), a ≠ 0 ∧ J.conj a = a ∧
      C.val.map J.conj = C.val ∧ C.val.transpose * S * C.val = a • J.form := by
  let K := FixedBy.subfield E J.conj
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite K
  have hk : Fintype.card K = p := by
    change Nat.card K = p at hfixed
    simpa only [Nat.card_eq_fintype_card] using hfixed
  let := charP_of_card_eq_prime hk
  have h2 : (2 : K) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime K (p := p)
    Nat.prime_two (by intro h; rw [h] at ho; norm_num at ho)
  let := invertibleOfNonzero h2
  let S₀ : Matrix (Fin 3) (Fin 3) K := fun i j =>
    ⟨S i j, congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M i j) hfix⟩
  have hm : S₀.map K.subtype = S := rfl
  have hs₀ : S₀.transpose = S₀ := by
    ext i j
    exact congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M i j) hs
  have hd₀ : S₀.det ≠ 0 := by
    intro h
    apply hd
    have hh := congrArg K.subtype h
    rw [RingHom.map_det, map_zero] at hh
    exact hh
  obtain ⟨a, C, ha, hC⟩ := ternary_similarity h2 S₀ hs₀ hd₀
  refine ⟨a.val, GeneralLinearGroup.map K.subtype C, ?_, a.property, ?_, ?_⟩
  · exact fun h => ha (Subtype.ext h)
  · ext i j
    exact (C.val i j).property
  · have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M.map K.subtype) hC
    change (C.val.map K.subtype).transpose * S * C.val.map K.subtype = a.val • J.form
    rw [hJ]
    have ht : ((a • !![0, 0, 1; 0, 1, 0; 1, 0, 0]) : Matrix (Fin 3) (Fin 3) K).map
        K.subtype = a.val • !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    simpa only [Matrix.map_mul, Matrix.transpose_map, hm, ht] using hh

end BenderSuzuki.MatrixGroups.HermitianForm.OddInvolutionNormalization
