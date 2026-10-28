module

public import Theory.Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra.WeightDecomposition
public import Mathlib.Algebra.DirectSum.LinearMap

/-!
# Local torus and normalizer traces for the Hall--Janko action

On each simultaneous weight space the literal word xᵃyᵇ is scalar, giving
its trace as the weight sum. The square of the normalizer moves every nonzero
weight, so its diagonal blocks and trace vanish. Both calculations apply to
all four patterns and hence do not depend on the cubic exclusion.

Source: Aschbacher--Smith K.4.5, printed p.460; Hiss--Malle corrected
Table 2, the characteristic-two degree-six J₂ entry. See ../Source.md.
-/

@[expose] public noncomputable section

namespace Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra
open Sporadic.LeechRelated.J2 Polynomial
open scoped BigOperators DirectSum
variable {E U : Type*} [Field E] [AddCommGroup U] [Module E U]

private theorem pow_apply_of_eigenvector (f : Module.End E U) {a : E} {v : U}
    (hv : f v = a • v) (n : ℕ) : (f ^ n) v = a ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv, smul_smul,
      pow_succ]

/-- The literal torus word acts by the corresponding product of eigenvalues. -/
theorem torus_action (ρ : Representation E Carrier U) (ζ : E)
    (w : Weights.Weight) (a b : ℕ) {v : U} (hv : v ∈ weightSpace ρ ζ w) :
    ρ (TraceGeometry.x ^ a * TraceGeometry.y ^ b) v =
      (ζ ^ (w.1.val * a + w.2.val * b)) • v := by
  have hx := Module.End.mem_eigenspace_iff.mp hv.1
  have hy := Module.End.mem_eigenspace_iff.mp hv.2
  rw [map_mul, Module.End.mul_apply, map_pow, map_pow,
    pow_apply_of_eigenvector _ hy, map_smul, pow_apply_of_eigenvector _ hx, smul_smul,
    ← pow_mul, ← pow_mul, mul_comm, ← pow_add]

/-- The trace on each literal torus word is its simultaneous weight sum. -/
theorem character_torus [CharP E 2] [IsAlgClosed E] [FiniteDimensional E U]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5) (a b : ℕ) :
    ρ.character (TraceGeometry.x ^ a * TraceGeometry.y ^ b) =
      ∑ w : Weights.Weight, (weightMultiplicity ρ ζ w : E) *
        ζ ^ (w.1.val * a + w.2.val * b) := by
  classical
  let f := ρ (TraceGeometry.x ^ a * TraceGeometry.y ^ b)
  have hf (w) : Set.MapsTo f (weightSpace ρ ζ w) (weightSpace ρ ζ w) := by
    intro v hv
    change ρ (TraceGeometry.x ^ a * TraceGeometry.y ^ b) v ∈ _
    rw [torus_action ρ ζ w a b hv]
    exact (weightSpace ρ ζ w).smul_mem _ hv
  change LinearMap.trace E U f = _
  rw [LinearMap.trace_eq_sum_trace_restrict (weightSpace_isInternal ρ hζ) hf]
  apply Finset.sum_congr rfl
  intro w _
  have he : f.restrict (hf w) =
      ζ ^ (w.1.val * a + w.2.val * b) • LinearMap.id := by
    ext v
    exact torus_action ρ ζ w a b v.property
  rw [he, map_smul, LinearMap.trace_id, smul_eq_mul, finrank_weightSpace, mul_comm]

/-- Substitution of any of the four proved patterns into the actual torus trace. -/
theorem character_torus_of_pattern [CharP E 2] [IsAlgClosed E] [FiniteDimensional E U]
    (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5)
    (i : Fin 4) (hi : ∀ w, weightMultiplicity ρ ζ w = Weights.pattern i w) (a b : ℕ) :
    ρ.character (TraceGeometry.x ^ a * TraceGeometry.y ^ b) =
      ∑ w : Weights.Weight, (Weights.pattern i w : E) *
        ζ ^ (w.1.val * a + w.2.val * b) := by
  simp only [character_torus ρ hζ, hi]

/-- Iterates of the inverse normalizer rotate the actual simultaneous spaces. -/
theorem inverse_rotation_iterate_mapsTo (ρ : Representation E Carrier U)
    {ζ : E} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) (w : Weights.Weight) :
    Set.MapsTo (ρ (TraceGeometry.r⁻¹ ^ n)) (weightSpace ρ ζ w)
      (weightSpace ρ ζ ((Weights.rotate^[n]) w)) := by
  induction n with
  | zero =>
    intro v hv
    simpa only [pow_zero, map_one, Module.End.one_apply, Function.iterate_zero_apply] using hv
  | succ n ih =>
    intro v hv
    rw [pow_succ', map_mul, Module.End.mul_apply, Function.iterate_succ_apply']
    exact inverse_rotation_mapsTo ρ hζ _ (ih hv)

private def rotateFourNonzero (w : {w : Weights.Weight // w ≠ 0}) :
    {w : Weights.Weight // w ≠ 0} :=
  ⟨(Weights.rotate^[4]) w.val, (by decide +kernel :
    ∀ w : Weights.Weight, w ≠ 0 → (Weights.rotate^[4]) w ≠ 0) w.val w.property⟩

/-- The normalizer square has trace zero because it moves every nonzero weight. -/
theorem character_r_sq [CharP E 2] [IsAlgClosed E] [FiniteDimensional E U]
    (ρ : Representation E Carrier U) (hρ : Function.Injective ρ)
    (hdim : Module.finrank E U = 6) {ζ : E} (hζ : IsPrimitiveRoot ζ 5) :
    ρ.character (TraceGeometry.r ^ 2) = 0 := by
  classical
  obtain ⟨i, hi⟩ := four_patterns ρ hρ hdim hζ
  have hz : weightSpace ρ ζ 0 = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    exact (hi 0).trans (Weights.pattern_zero i)
  have hn : DirectSum.IsInternal (fun w : {w : Weights.Weight // w ≠ 0} =>
      weightSpace ρ ζ w.val) := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact (weightSpace_independent ρ hζ).comp Subtype.val_injective
    · apply top_unique
      rw [← iSup_weightSpace_eq_top ρ hζ]
      refine iSup_le fun w => ?_
      by_cases hw : w = 0
      · simp [hw, hz]
      · exact le_iSup (fun w : {w : Weights.Weight // w ≠ 0} => weightSpace ρ ζ w.val) ⟨w, hw⟩
  have hr : TraceGeometry.r⁻¹ ^ 4 = TraceGeometry.r ^ 2 := by
    rw [inv_pow]
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_add]
    exact TraceGeometry.r_pow_six
  change LinearMap.trace E U (ρ (TraceGeometry.r ^ 2)) = 0
  apply LinearMap.trace_eq_zero_of_mapsTo_ne hn rotateFourNonzero
    (by decide +kernel)
  intro w
  simpa only [hr, rotateFourNonzero] using inverse_rotation_iterate_mapsTo ρ hζ 4 w.val

/-- The prescribed fifth-order triangle generator has the finite-certificate
exponent on each actual simultaneous weight space. -/
theorem d_action (ρ : Representation E Carrier U) {ζ : E} (hζ : IsPrimitiveRoot ζ 5)
    (w : Weights.Weight) {v : U} (hv : v ∈ weightSpace ρ ζ w) :
    ρ TraceGeometry.d v = ζ ^ (Weights.dExponent w).val • v := by
  have hy : TraceGeometry.y⁻¹ ^ 2 = TraceGeometry.y ^ 3 := by
    rw [inv_pow]
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_add]
    exact TraceGeometry.y_pow_five
  have he : ((w.1.val + w.2.val * 3 : ℕ) : ZMod 5) = Weights.dExponent w := by
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_ofNat, Weights.dExponent]
    rw [show (3 : ZMod 5) = -2 by decide]
    ring
  have he' : (w.1.val + w.2.val * 3) % 5 = (Weights.dExponent w).val := by
    rw [← ZMod.val_natCast]
    exact congrArg ZMod.val he
  have ht := torus_action ρ ζ w 1 3 hv
  simp only [pow_one, Nat.mul_one] at ht
  rw [← hy, ← TraceGeometry.d_eq] at ht
  rw [pow_eq_pow_mod _ hζ.pow_eq_one, he'] at ht
  exact ht

end Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra
