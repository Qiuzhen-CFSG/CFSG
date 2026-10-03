module
public import Theory.Character.ModularBlock.RelativeTraceKernel
public import Theory.Character.ModularBlock.JacobsonFiniteAlgebra

/-!
# Exact relative traces inside an idempotent corner

Over a commutative local ring, a conjugation-fixed idempotent in a finite
group algebra is an exact relative trace if its coefficients at the fixed
group elements belong to the maximal ideal. The acting element need only
have square one. The tracing element stays in the original idempotent
corner, a condition needed by the subsequent projectivity argument.

First obtain a relative trace modulo the maximal ideal by coefficient
pairing. Sandwich its error by the idempotent. The resulting invariant
error has all coefficients in the maximal ideal, so the Jacobson
finite-algebra theorem makes one minus that error invertible. Its inverse
is conjugation-fixed and commutes with the idempotent. Multiplying the
sandwiched tracing element by this inverse removes the error and preserves
the corner condition.

This ports the order-two form of Feit III.6.6(ii) formalized in
`Submission/ZStar/ExactRelativeTrace.lean` at revision `c3503435` of
`public/lean-eval/glauberman_zStar`. The exact historical statement is
preserved using the current group-algebra coefficient interface.
-/

noncomputable section

namespace ModularBlock
namespace ExactRelativeTrace

universe u v

attribute [local instance] Fintype.ofFinite

private lemma coeff_mem_ideal_mul_left
    {R G : Type*} [CommRing R] [Group G]
    (I : Ideal R) (a q : MonoidAlgebra R G)
    (hq : ∀ x : G, q.coeff x ∈ I) :
    ∀ x : G, (a * q).coeff x ∈ I := by
  intro x
  rw [MonoidAlgebra.coeff_mul_apply_left]
  change a.coeff.support.sum (fun g ↦ a.coeff g * q.coeff (g⁻¹ * x)) ∈ I
  apply I.sum_mem
  intro g hg
  exact I.mul_mem_left _ (hq _)

private lemma coeff_mem_ideal_mul_right
    {R G : Type*} [CommRing R] [Group G]
    (I : Ideal R) (q a : MonoidAlgebra R G)
    (hq : ∀ x : G, q.coeff x ∈ I) :
    ∀ x : G, (q * a).coeff x ∈ I := by
  intro x
  rw [MonoidAlgebra.coeff_mul_apply_right]
  change a.coeff.support.sum (fun g ↦ q.coeff (x * g⁻¹) * a.coeff g) ∈ I
  apply I.sum_mem
  intro g hg
  exact I.mul_mem_right _ (hq _)

private lemma conjugation_involution
    {R G : Type*} [CommRing R] [Group G]
    (z : G) (hz : z * z = 1) (a : MonoidAlgebra R G) :
    BrauerKernelRelativeTrace.conjugation R z
        (BrauerKernelRelativeTrace.conjugation R z a) = a := by
  ext x
  rw [BrauerKernelRelativeTrace.conjugation_apply,
    BrauerKernelRelativeTrace.conjugation_apply]
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  simp only [hzinv]
  congr 1
  calc
    z * (z * x * z) * z = (z * z) * x * (z * z) := by
      simp only [mul_assoc]
    _ = x := by rw [hz, one_mul, mul_one]

/-- Order-two form of Feit's III.6.6(ii).  A conjugation-fixed idempotent
whose coefficients on the conjugation fixed points vanish modulo the maximal
ideal is an exact relative trace from the trivial subgroup.  The tracing
element is retained in the idempotent corner. -/
public theorem exists_exact_relativeTrace_of_fixed_coeff_mem_maximalIdeal
    {R G : Type*} [CommRing R] [IsLocalRing R] [Group G] [Finite G]
    (z : G) (hz : z * z = 1)
    (f : MonoidAlgebra R G) (hf : IsIdempotentElem f)
    (hfinv : BrauerKernelRelativeTrace.conjugation R z f = f)
    (hfixed : ∀ x : G, z⁻¹ * x * z = x →
      f.coeff x ∈ IsLocalRing.maximalIdeal R) :
    ∃ c : MonoidAlgebra R G,
      f * c * f = c ∧
      f = c + BrauerKernelRelativeTrace.conjugation R z c := by
  classical
  let I : Ideal R := IsLocalRing.maximalIdeal R
  obtain ⟨b, hb⟩ :=
    BrauerKernelRelativeTrace.exists_relativeTrace_mod_ideal_of_conjugation_fixed
      z hz I f hfinv hfixed
  let d : MonoidAlgebra R G :=
    f - (b + BrauerKernelRelativeTrace.conjugation R z b)
  have hdcoeff : ∀ x : G, d.coeff x ∈ I := by
    intro x
    exact hb x
  have hconjtrace :
      BrauerKernelRelativeTrace.conjugation R z
          (b + BrauerKernelRelativeTrace.conjugation R z b) =
        b + BrauerKernelRelativeTrace.conjugation R z b := by
    rw [map_add, conjugation_involution z hz]
    exact add_comm _ _
  have hdInv : BrauerKernelRelativeTrace.conjugation R z d = d := by
    dsimp [d]
    rw [map_sub, hfinv, hconjtrace]
  let c₀ : MonoidAlgebra R G := f * b * f
  let r : MonoidAlgebra R G := f * d * f
  have hrcoeff : ∀ x : G, r.coeff x ∈ I := by
    have hleft := coeff_mem_ideal_mul_left I f d hdcoeff
    exact coeff_mem_ideal_mul_right I (f * d) f hleft
  have hrInv : BrauerKernelRelativeTrace.conjugation R z r = r := by
    dsimp [r]
    rw [map_mul, map_mul, hfinv, hdInv]
  have hc₀trace :
      c₀ + BrauerKernelRelativeTrace.conjugation R z c₀ = f - r := by
    have hdrel :
        b + BrauerKernelRelativeTrace.conjugation R z b = f - d := by
      dsimp [d]
      simp
    calc
      c₀ + BrauerKernelRelativeTrace.conjugation R z c₀ =
          f * (b + BrauerKernelRelativeTrace.conjugation R z b) * f := by
            dsimp [c₀]
            rw [map_mul, map_mul, hfinv]
            rw [mul_add, add_mul]
      _ = f * (f - d) * f := by rw [hdrel]
      _ = (f * f) * f - (f * d) * f := by rw [mul_sub, sub_mul]
      _ = f - r := by
        rw [hf, hf]
  have hfr : f * r = r := by
    dsimp [r]
    calc
      f * (f * d * f) = (f * f) * d * f := by ac_rfl
      _ = f * d * f := by rw [hf]
  have hrf : r * f = r := by
    dsimp [r]
    calc
      f * d * f * f = f * d * (f * f) := by ac_rfl
      _ = f * d * f := by rw [hf]
  have hcomm : Commute f (1 - r) := by
    rw [commute_iff_eq]
    rw [mul_sub, mul_one, sub_mul, one_mul, hfr, hrf]
  have hunit : IsUnit (1 - r) :=
    JacobsonFiniteAlgebra.groupAlgebra_isUnit_one_sub_of_coeff_mem_maximalIdeal
      r hrcoeff
  let U : (MonoidAlgebra R G)ˣ := hunit.unit
  have hU : (U : MonoidAlgebra R G) = 1 - r := hunit.unit_spec
  let u : MonoidAlgebra R G := ↑U⁻¹
  have hmulInv : (1 - r) * u = 1 := by
    rw [← hU]
    exact Units.mul_inv U
  have hinvMul : u * (1 - r) = 1 := by
    rw [← hU]
    exact Units.inv_mul U
  have hOneSubInv :
      BrauerKernelRelativeTrace.conjugation R z (1 - r) = 1 - r := by
    rw [map_sub, map_one, hrInv]
  have huInv : BrauerKernelRelativeTrace.conjugation R z u = u := by
    have hconjMul :
        (1 - r) * BrauerKernelRelativeTrace.conjugation R z u = 1 := by
      have h := congrArg
        (fun a : MonoidAlgebra R G ↦
          BrauerKernelRelativeTrace.conjugation R z a) hmulInv
      simpa only [map_mul, map_one, hOneSubInv] using h
    calc
      BrauerKernelRelativeTrace.conjugation R z u =
          1 * BrauerKernelRelativeTrace.conjugation R z u := by rw [one_mul]
      _ = (u * (1 - r)) *
          BrauerKernelRelativeTrace.conjugation R z u := by rw [hinvMul]
      _ = u * ((1 - r) *
          BrauerKernelRelativeTrace.conjugation R z u) := by rw [mul_assoc]
      _ = u := by rw [hconjMul, mul_one]
  have hcommu : Commute f u := by
    have hcommU : Commute f (U : MonoidAlgebra R G) := by
      rw [hU]
      exact hcomm
    exact hcommU.units_inv_right
  have hc₀left : f * c₀ = c₀ := by
    dsimp [c₀]
    calc
      f * (f * b * f) = (f * f) * b * f := by ac_rfl
      _ = f * b * f := by rw [hf]
  have hc₀right : c₀ * f = c₀ := by
    dsimp [c₀]
    calc
      f * b * f * f = f * b * (f * f) := by ac_rfl
      _ = f * b * f := by rw [hf]
  let c : MonoidAlgebra R G := c₀ * u
  have hcorner : f * c * f = c := by
    dsimp [c]
    calc
      f * (c₀ * u) * f = (f * c₀) * u * f := by ac_rfl
      _ = c₀ * u * f := by rw [hc₀left]
      _ = c₀ * (u * f) := mul_assoc _ _ _
      _ = c₀ * (f * u) := by rw [hcommu.eq]
      _ = (c₀ * f) * u := (mul_assoc _ _ _).symm
      _ = c₀ * u := by rw [hc₀right]
  have hexact :
      c + BrauerKernelRelativeTrace.conjugation R z c = f := by
    dsimp [c]
    rw [map_mul, huInv]
    calc
      c₀ * u +
          BrauerKernelRelativeTrace.conjugation R z c₀ * u =
          (c₀ + BrauerKernelRelativeTrace.conjugation R z c₀) * u := by
            rw [add_mul]
      _ = (f - r) * u := by rw [hc₀trace]
      _ = (f * (1 - r)) * u := by rw [mul_sub, mul_one, hfr]
      _ = f * ((1 - r) * u) := by rw [mul_assoc]
      _ = f := by rw [hmulInv, mul_one]
  exact ⟨c, hcorner, hexact.symm⟩

end ExactRelativeTrace
end ModularBlock

