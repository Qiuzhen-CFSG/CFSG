module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.HighestLine

/-!
# The positive primitive line from a contravariant form

A positive primitive vector pairs to zero against every nonempty negative
root word. Negative cyclicity therefore makes evaluation against the highest
vector injective on the primitive space. The nonzero highest vector is itself
primitive, so this space is its line.

The pairing is a genuine bilinear form on the given carrier, and all adjoints
are the actual first root coefficients. Its existence is an explicit premise
here; the rational-duality construction is separate.

Source: the contravariant formulation of Steinberg, *Representations of
Algebraic Groups* (1963), §§2, 4 and the primitive-vector argument in 11.1.
The linear-algebra argument adapts `ReeF4/.../PositivePrimitives/Pairing.lean`.
-/

open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity
@[expose] public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A nondegenerate form making positive and negative root coefficients adjoint.
This predicate specifies a form and does not assert its existence. -/
def HasContravariantPairing (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ) : Prop :=
  ∃ e : V →ₗ[k] Module.Dual k V,
    Function.Injective e ∧ ∀ (α : PositiveRoot S) (x y : V),
      e (rootOperator S ρ hρ α.val x) y =
        e x (rootOperator S ρ hρ (S.roots.neg α.val) y)

/-- A primitive vector is determined by its pairing with a negative-cyclic generator. -/
theorem primitive_eq_zero_of_pairing_highest_eq_zero (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ) (v : V)
    (hspan : negativeRootSpan S ρ hρ v = ⊤)
    (e : V →ₗ[k] Module.Dual k V) (he : Function.Injective e)
    (hcontra : ∀ (α : PositiveRoot S) (x y : V),
      e (rootOperator S ρ hρ α.val x) y =
        e x (rootOperator S ρ hρ (S.roots.neg α.val) y))
    {w : V} (hw : w ∈ positiveRootKernel S ρ hρ) (hwv : e w v = 0) : w = 0 := by
  have hkill : ∀ α : PositiveRoot S, rootOperator S ρ hρ α.val w = 0 := by
    simpa only [positiveRootKernel, Submodule.mem_iInf, LinearMap.mem_ker] using hw
  have hzero : e w = 0 := by
    apply LinearMap.ext
    intro z
    have hz : z ∈ negativeRootSpan S ρ hρ v := by rw [hspan]; trivial
    change e w z = 0
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, rfl⟩ := hz
      cases l with
      | nil => simpa using hwv
      | cons α l =>
        have hc := hcontra α w
          ((l.map fun β => rootOperator S ρ hρ (S.roots.neg β.val)).prod v)
        rw [hkill, map_zero, LinearMap.zero_apply] at hc
        simpa only [List.map_cons, List.prod_cons, Module.End.mul_apply] using hc.symm
    | zero => exact map_zero _
    | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
    | smul a x _ hx => simp only [map_smul, hx, smul_zero]
  exact he (hzero.trans e.map_zero.symm)

/-- Negative cyclicity and an actual nondegenerate contravariant form identify
the positive common kernel with the highest-vector line. -/
theorem positiveRootKernel_eq_span_of_contravariantPairing (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    {χ : TorusWeight S.torus} {v : V} (hv : HasHighWeight ρ S.borel S.torus v χ)
    (hspan : negativeRootSpan S ρ hρ v = ⊤)
    (hpair : HasContravariantPairing S ρ hρ) :
    positiveRootKernel S ρ hρ = Submodule.span k {v} := by
  obtain ⟨e, he, hc⟩ := hpair
  have hvk := highest_mem_positiveRootKernel S ρ hρ hv
  have hvv : e v v ≠ 0 := by
    intro hz
    exact hv.1.1
      (primitive_eq_zero_of_pairing_highest_eq_zero S ρ hρ v hspan e he hc hvk hz)
  apply le_antisymm
  · intro w hw
    let c := e w v / e v v
    have hzero : w - c • v = 0 := by
      apply primitive_eq_zero_of_pairing_highest_eq_zero S ρ hρ v hspan e he hc
        ((positiveRootKernel S ρ hρ).sub_mem hw ((positiveRootKernel S ρ hρ).smul_mem c hvk))
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul, c, div_mul_cancel₀ _ hvv, sub_self]
    exact Submodule.mem_span_singleton.mpr ⟨c, (sub_eq_zero.mp hzero).symm⟩
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr hvk

end
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity
