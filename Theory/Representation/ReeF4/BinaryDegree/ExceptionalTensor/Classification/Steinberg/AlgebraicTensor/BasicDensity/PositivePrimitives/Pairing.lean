module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.RootDuality.Negation

/-!
# The primitive line from a contravariant pairing

A vector in the common positive short-root kernel pairs to zero against every
nonempty negative short-root word. If those words span from `v`, the functional
obtained by pairing with `v` is therefore injective on the primitive space.
Since the genuine highest vector is primitive and nonzero, the primitive space
is its line.

The construction of the nondegenerate contravariant pairing on the actual
algebraic representation is a separate obligation. No existence is asserted
here. In particular the primitive-line result below retains this explicit
premise and does not infer it from negative cyclicity alone.

Source: the contravariant-duality formulation of the primitive-vector argument
in Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J. 22 (1963),
§§2, 4, and 11.1(1),(3), DOI 10.1017/S0027763000011016.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
variable {F : Type*} [Field F] [IsAlgClosed F]
noncomputable local instance shortPairingRootNeg : InvolutiveNeg F4Chevalley.Root :=
  typeF4RootPairing.indexNeg

/-- A left nondegenerate pairing making opposite short-root coefficients adjoint.
This is a condition on the actual coefficient action, not an existence assertion. -/
@[expose] def RootExpansion.HasShortContravariantPairing {B : AlgebraicFactor F}
    (p : RootExpansion B.action) : Prop :=
  ∃ e : B.Space →ₗ[F] Module.Dual F B.Space,
    Function.Injective e ∧ ∀ (r : ShortPositiveRoot) (x y : B.Space),
      e (p.coeff r.val 1 x) y = e x (p.coeff (-r.val) 1 y)

/-- Against a contravariant pairing, a primitive vector is determined by its
value on a negative-cyclic generator. -/
theorem RootExpansion.primitive_eq_zero_of_pairing_highest_eq_zero
    {B : AlgebraicFactor F} (p : RootExpansion B.action) (v : B.Space)
    (hspan : p.shortNegativeSpan v = ⊤)
    (e : B.Space →ₗ[F] Module.Dual F B.Space) (he : Function.Injective e)
    (hcontra : ∀ (r : ShortPositiveRoot) (x y : B.Space),
      e (p.coeff r.val 1 x) y = e x (p.coeff (-r.val) 1 y))
    {w : B.Space} (hw : w ∈ p.shortPositiveKernel) (hwv : e w v = 0) : w = 0 := by
  have hkill : ∀ r : ShortPositiveRoot, p.coeff r.val 1 w = 0 := by
    simpa only [RootExpansion.shortPositiveKernel, Submodule.mem_iInf, LinearMap.mem_ker]
      using hw
  have hzero : e w = 0 := by
    apply LinearMap.ext
    intro z
    have hz : z ∈ p.shortNegativeSpan v := by rw [hspan]; trivial
    change e w z = 0
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, rfl⟩ := hz
      cases l with
      | nil => simpa using hwv
      | cons r l =>
        let s : ShortPositiveRoot := ⟨-r.val,
          fun h => r.property.1 ((isLongRoot_neg_iff r.val).mp h),
          (RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base r.val).mpr
            r.property.2⟩
        have hc := hcontra s w ((l.map fun r => p.coeff r.val 1).prod v)
        rw [hkill, map_zero, LinearMap.zero_apply] at hc
        simpa only [s, neg_neg, List.map_cons, List.prod_cons, Module.End.mul_apply]
          using hc.symm
    | zero => exact map_zero _
    | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
    | smul a x _ hx => simp only [map_smul, hx, smul_zero]
  exact he (hzero.trans e.map_zero.symm)

/-- Negative cyclicity and a nondegenerate contravariant pairing force the
positive primitive space to be precisely the highest-vector line. -/
theorem RootExpansion.shortPositiveKernel_eq_span_of_contravariantPairing
    {B : AlgebraicFactor F} (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v) (hspan : p.shortNegativeSpan v = ⊤)
    (hpair : p.HasShortContravariantPairing) :
    p.shortPositiveKernel = Submodule.span F {v} := by
  obtain ⟨e, he, hc⟩ := hpair
  have hvk := p.highest_mem_shortPositiveKernel hv
  have hvv : e v v ≠ 0 := by
    intro hz
    exact hv.1 (p.primitive_eq_zero_of_pairing_highest_eq_zero v hspan e he hc hvk hz)
  apply le_antisymm
  · intro w hw
    let c := e w v / e v v
    have hzero : w - c • v = 0 := by
      apply p.primitive_eq_zero_of_pairing_highest_eq_zero v hspan e he hc
        (p.shortPositiveKernel.sub_mem hw (p.shortPositiveKernel.smul_mem c hvk))
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul, c, div_mul_cancel₀ _ hvv, sub_self]
    exact Submodule.mem_span_singleton.mpr ⟨c, (sub_eq_zero.mp hzero).symm⟩
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr hvk
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
