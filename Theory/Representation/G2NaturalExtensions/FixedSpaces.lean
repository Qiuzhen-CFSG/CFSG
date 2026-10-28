module

public import Theory.Representation.G2NaturalExtensions

/-!
# Fixed vectors in central natural G₂ extensions

An automorphism fixing the image of a trace-zero octonion moves it by a scalar
identity. The scalar line is the polar radical, and the norm of its identity is
one. Norm preservation therefore makes the square of that scalar zero, hence
the scalar itself zero. Every derived-generated central natural extension is
a quotient of this Weyl module, so the same fixed-vector implication descends.

This proves the geometric input to Aschbacher–Smith B.4.6(7), printed p.88,
for all elements of the actual G₂ model, including the binary exception.
The universal cover used here retains the distinction between G₂ and G₂′.
-/

@[expose] public section

open Atlas.SplitOctonion Representation
open Atlas.G2.Natural

namespace Atlas.G2.Natural.Extensions
variable {F : Type*} [Field F] [CharP F 2]

/-- An octonion automorphism fixing a natural vector fixes every trace-zero
representative. Norm preservation kills its possible scalar displacement. -/
theorem traceZero_fixed_of_natural_fixed (g : Model F) (x : TraceZero F)
    (hx : action F g (mk F x) = mk F x) : traceZeroAction F g x = x := by
  obtain ⟨c, hc⟩ := (mk_eq_mk_iff F (traceZeroAction F g x) x).mp hx
  have hmove : g.val x.val = c • unit + x.val := by
    exact (eq_sub_iff_add_eq.mp hc).symm
  have hpolar : normPolar (c • unit) x.val = 0 := by
    rw [map_smul, LinearMap.smul_apply, OrthogonalCover.polar_unit,
      show trace x.val = 0 from x.property, smul_zero]
  have hn := automorphism_norm g x.val
  rw [hmove, norm_add, SplitOctonion.norm_smul, hpolar] at hn
  have hunit : norm (unit : Carrier F) = 1 := by simp [SplitOctonion.norm, unit]
  rw [hunit, mul_one, add_zero] at hn
  have hc0 : c = 0 := sq_eq_zero_iff.mp (add_right_cancel (hn.trans (zero_add _).symm))
  apply Subtype.ext
  rw [traceZeroAction_val, hmove, hc0, zero_smul, zero_add]
end Atlas.G2.Natural.Extensions

namespace Atlas.G2.Natural.Extensions
open Representation.OneCohomology
variable {F V : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The fixed-vector implication descends to every derived-generated central
natural extension through its universal Weyl quotient. -/
theorem fixed_of_natural_fixed (σ : Representation (ZMod 2) (Model F) V)
    (p : V →ₗ[ZMod 2] Space F) (hp : Function.Surjective p)
    (hfixed : p.ker ≤ fixed σ)
    (hgen : Coinvariants.ker (σ.comp (commutator (Model F)).subtype) = ⊤)
    (he : ∀ g v, p (σ g v) = action F g (p v))
    (g : Model F) (v : V) (hv : action F g (p v) = p v) : σ g v = v := by
  obtain ⟨f, hf, heq, hover⟩ := exists_weyl_quotient σ p hp hfixed hgen he
  obtain ⟨w, rfl⟩ := hf v
  have hfix : traceZeroAction F g w = w := by
    apply traceZero_fixed_of_natural_fixed
    simpa only [hover] using hv
  rw [← heq, hfix]
end Atlas.G2.Natural.Extensions
