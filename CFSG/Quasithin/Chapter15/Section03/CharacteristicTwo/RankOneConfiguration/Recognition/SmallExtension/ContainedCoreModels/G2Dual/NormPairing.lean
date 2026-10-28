module

public import Theory.Representation.G2Natural
public import Theory.AtlasPort.Algebra.SplitOctonion.NormGeometry
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The norm pairing on the natural G₂ quotient

The polar form of the split-octonion norm restricts to the trace-zero
hyperplane. The scalar identity line lies in both radicals. Testing against
the six off-diagonal basis vectors proves that it is the entire radical,
so the descended form identifies the six-dimensional quotient with its dual.
Invariance under the actual octonion automorphisms gives equivariance for
the contragredient action, with its inverse in the argument of a functional.

This supplies the self-duality used for G₂ covering modules in
Aschbacher–Smith, I.1.5–6 (printed p.408), C.1.30 (p.135), and the proof of
15.3.31 (p.1132 / PDF p.1149). The model and norm conventions are inherited
from the licensed ATLAS ports; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. No additional ATLAS source is copied here.
-/

public section

open Atlas.SplitOctonion
namespace Atlas.G2.Natural
variable (K : Type*) [Field K] [CharP K 2]

private def tracePairing : TraceZero K →ₗ[K] TraceZero K →ₗ[K] K :=
  normPolar.compl₁₂ (TraceZero K).subtype (TraceZero K).subtype

private theorem scalarLine_radical : scalarLine K ≤ (tracePairing K).ker := by
  apply Submodule.span_le.mpr
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  apply LinearMap.ext
  intro y
  change normPolar unit y.val = 0
  have hy : y.val 3 + y.val 4 = 0 := y.property
  simpa [normPolar, unit, add_comm] using hy

private theorem scalarLine_flip_radical : scalarLine K ≤ (tracePairing K).flip.ker := by
  intro x hx
  apply LinearMap.ext
  intro y
  change normPolar y.val x.val = 0
  rw [normPolar_symm]
  exact LinearMap.congr_fun (scalarLine_radical K hx) y

/-- The polar norm form descended through the scalar identity in both variables. -/
noncomputable def quotientNormPairing : Space K →ₗ[K] Module.Dual K (Space K) :=
  (tracePairing K).liftQ₂ (scalarLine K) (scalarLine K)
    (scalarLine_radical K) (scalarLine_flip_radical K)

/-- The pairing is computed on any trace-zero octonion representatives. -/
@[simp] theorem quotientNormPairing_mk (x y : TraceZero K) :
    quotientNormPairing K (mk K x) (mk K y) = normPolar x.val y.val := by
  simp [quotientNormPairing, mk, tracePairing]

/-- The descended form is nondegenerate: its trace-zero radical was precisely scalar. -/
theorem quotientNormPairing_injective : Function.Injective (quotientNormPairing K) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro v hv
  obtain ⟨x, rfl⟩ := mk_surjective K v
  have h (y : TraceZero K) : normPolar x.val y.val = 0 :=
    LinearMap.congr_fun hv (mk K y)
  have h0 : x.val 0 = 0 := by
    simpa [normPolar, basisVector] using
      h ⟨basisVector 7, by simp [mem_traceZero, trace, basisVector]⟩
  have h1 : x.val 1 = 0 := by
    simpa [normPolar, basisVector] using
      h ⟨basisVector 6, by simp [mem_traceZero, trace, basisVector]⟩
  have h2 : x.val 2 = 0 := by
    simpa [normPolar, basisVector] using
      h ⟨basisVector 5, by simp [mem_traceZero, trace, basisVector]⟩
  have h5 : x.val 5 = 0 := by
    simpa [normPolar, basisVector] using
      h ⟨basisVector 2, by simp [mem_traceZero, trace, basisVector]⟩
  have h6 : x.val 6 = 0 := by
    simpa [normPolar, basisVector] using
      h ⟨basisVector 1, by simp [mem_traceZero, trace, basisVector]⟩
  have h7 : x.val 7 = 0 := by
    simpa [normPolar, basisVector] using
      h ⟨basisVector 0, by simp [mem_traceZero, trace, basisVector]⟩
  have ht : x.val 3 = x.val 4 := by
    have hx : x.val 3 + x.val 4 = 0 := x.property
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hx
  exact (mk_eq_zero_iff K x).mpr ⟨x.val 3, by
    ext i
    fin_cases i <;> simp [unit, h0, h1, h2, h5, h6, h7, ht]⟩

/-- The actual natural octonion quotient is linearly self-dual. -/
noncomputable def quotientNormDualEquiv : Space K ≃ₗ[K] Module.Dual K (Space K) :=
  LinearEquiv.ofBijective (quotientNormPairing K) ⟨quotientNormPairing_injective K,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp
      (quotientNormPairing_injective K)⟩

/-- Every octonion automorphism preserves the descended pairing. -/
theorem quotientNormPairing_invariant (g : Model K) (v w : Space K) :
    quotientNormPairing K (action K g v) (action K g w) = quotientNormPairing K v w := by
  obtain ⟨x, rfl⟩ := mk_surjective K v
  obtain ⟨y, rfl⟩ := mk_surjective K w
  change normPolar (g.val x.val) (g.val y.val) = normPolar x.val y.val
  exact automorphism_normPolar g x.val y.val

/-- The norm self-duality intertwines the full natural and contragredient actions. -/
theorem quotientNormDualEquiv_equivariant (g : Model K) (v : Space K) :
    quotientNormDualEquiv K (action K g v) =
      (action K).dual g (quotientNormDualEquiv K v) := by
  apply LinearMap.ext
  intro w
  change quotientNormPairing K (action K g v) w =
    quotientNormPairing K v (action K g⁻¹ w)
  have h : action K g (action K g⁻¹ w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  simpa only [h] using quotientNormPairing_invariant K g v (action K g⁻¹ w)
end Atlas.G2.Natural
