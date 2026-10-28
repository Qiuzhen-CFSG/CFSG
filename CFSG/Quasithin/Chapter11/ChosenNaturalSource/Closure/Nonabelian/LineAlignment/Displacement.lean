module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment.Action

/-!
# A field twist cannot move a plane inside a field line

For a semilinear map e with coefficient automorphism σ, subtracting σ(t)
 times the displacement of v from the displacement of tv gives (σ(t)-t)v.
If σ(t) differs from t and every displacement lies in one field line, the
whole plane lies in that line, contradicting its dimension.

The original-action application is in Plane.lean. It includes the degree-two
field-automorphism possibility in 11.5.3 without excluding the field of order
four or presupposing field-linearity of the Sylow action.
Source: Aschbacher--Smith, 11.5.3(3), printed pp.779--780.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment.PlaneDisplacement
variable {F N : Type*} [Field F] [AddCommGroup N] [Module F N]

theorem field_twist_eq_one [FiniteDimensional F N]
    (e : N →+ N) (σ : F ≃+* F)
    (hs : ∀ t v, e (t • v) = σ t • e v)
    (P Q : Submodule F N) (hP : Module.finrank F P = 2)
    (hQ : Module.finrank F Q = 1)
    (hd : ∀ v ∈ P, e v - v ∈ Q) : σ = RingEquiv.refl F := by
  ext t
  by_contra ht
  have ht' : σ t - t ≠ 0 := sub_ne_zero.mpr ht
  have hPQ : P ≤ Q := by
    intro v hv
    have hv' : (σ t - t) • v ∈ Q := by
      have h := Q.sub_mem (hd (t • v) (P.smul_mem t hv)) (Q.smul_mem (σ t) (hd v hv))
      convert h using 1
      rw [hs]
      module
    have h := Q.smul_mem (σ t - t)⁻¹ hv'
    simpa only [smul_smul, inv_mul_cancel₀ ht', one_smul] using h
  have h := Submodule.finrank_mono hPQ
  omega

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment.PlaneDisplacement
