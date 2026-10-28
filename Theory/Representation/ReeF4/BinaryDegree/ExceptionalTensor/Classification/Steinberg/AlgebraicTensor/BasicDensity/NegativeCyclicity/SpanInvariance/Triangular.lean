module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.Basic

/-!
# Triangular commutation on the negative short-word span

Let `N` be the span of the first coefficients at negative short roots. If a
space `L` of operators sends the initial vector into its negative word span
and satisfies `[L,N] ⊆ L + N`, induction on word length proves that `L`
preserves that span. The induction is simultaneous in every operator of `L`;
it does not assume beforehand that commutator operators preserve the span.

We apply this to the span of positive root coefficients and the four simple
Cartan commutators. The actual coefficient bracket identities remain explicit
inputs. No adjoint-matrix identity is silently transferred to the arbitrary
rational representation.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), §§2, 4 and the first part of 11.1(1), pp. 52–53;
DOI 10.1017/S0027763000011016.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance spanInvarianceTriangularNeg : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

namespace NegativeCyclicity.SpanInvariance

/-- Positive roots in the fixed F₄ base, of either length. -/
abbrev PositiveRoot := {r : F4Chevalley.Root // typeF4RootPairing_base.IsPos r}

/-- The linear span of the actual negative short-root coefficients. -/
@[expose] def negativeOperators {B : AlgebraicFactor F} (p : RootExpansion B.action) :
    Submodule F (Module.End F B.Space) :=
  Submodule.span F (Set.range fun s : ShortNegativeRoot => p.coeff s.val 1)

/-- The linear span of the actual positive root coefficients. -/
@[expose] def positiveOperators {B : AlgebraicFactor F} (p : RootExpansion B.action) :
    Submodule F (Module.End F B.Space) :=
  Submodule.span F (Set.range fun r : PositiveRoot => p.coeff r.val 1)

/-- The simple Cartan commutator, formed from the actual representation coefficients. -/
@[expose] def cartanOperator {B : AlgebraicFactor F} (p : RootExpansion B.action) (i : Fin 4) :
    Module.End F B.Space :=
  p.coeff (typeF4SimpleRootIndex i) 1 * p.coeff (-typeF4SimpleRootIndex i) 1 -
    p.coeff (-typeF4SimpleRootIndex i) 1 * p.coeff (typeF4SimpleRootIndex i) 1

/-- The span of the four simple Cartan commutators. -/
@[expose] def cartanOperators {B : AlgebraicFactor F} (p : RootExpansion B.action) :
    Submodule F (Module.End F B.Space) :=
  Submodule.span F (Set.range (cartanOperator p))

/-- Positive root coefficients together with the simple Cartan commutators. -/
@[expose] def nonnegativeOperators {B : AlgebraicFactor F} (p : RootExpansion B.action) :
    Submodule F (Module.End F B.Space) := positiveOperators p ⊔ cartanOperators p

/-- Every linear combination of negative short generators preserves their word span. -/
theorem negativeOperators_stable {B : AlgebraicFactor F} (p : RootExpansion B.action)
    (v : B.Space) {A : Module.End F B.Space} (hA : A ∈ negativeOperators p) :
    ∀ w ∈ p.shortNegativeSpan v, A w ∈ p.shortNegativeSpan v := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨r, rfl⟩ := hA
    exact fun _ hw => p.coeff_mem_shortNegativeSpan v r hw
  | zero => simp
  | add A D hA hD ihA ihD =>
    intro w hw
    exact (p.shortNegativeSpan v).add_mem (ihA w hw) (ihD w hw)
  | smul c A hA ihA =>
    intro w hw
    exact (p.shortNegativeSpan v).smul_mem c (ihA w hw)

/-- Triangular commutation propagates initial-vector membership along every negative word. -/
theorem stable_of_triangular_commutators {B : AlgebraicFactor F}
    (p : RootExpansion B.action) (v : B.Space) (L : Submodule F (Module.End F B.Space))
    (hinit : ∀ A ∈ L, A v ∈ p.shortNegativeSpan v)
    (hcomm : ∀ A ∈ L, ∀ s : ShortNegativeRoot,
      A * p.coeff s.val 1 - p.coeff s.val 1 * A ∈ L ⊔ negativeOperators p) :
    ∀ A ∈ L, ∀ w ∈ p.shortNegativeSpan v, A w ∈ p.shortNegativeSpan v := by
  have hword (l : List ShortNegativeRoot) : ∀ A ∈ L,
      A ((l.map fun s => p.coeff s.val 1).prod v) ∈ p.shortNegativeSpan v := by
    induction l with
    | nil => simpa using hinit
    | cons s l ih =>
      intro A hA
      let w := (l.map fun s => p.coeff s.val 1).prod v
      have hw : w ∈ p.shortNegativeSpan v := Submodule.subset_span ⟨l, rfl⟩
      obtain ⟨D, hD, N, hN, he⟩ := Submodule.mem_sup.mp (hcomm A hA s)
      have hc : (A * p.coeff s.val 1 - p.coeff s.val 1 * A) w ∈ p.shortNegativeSpan v := by
        rw [← he]
        exact (p.shortNegativeSpan v).add_mem (ih D hD) (negativeOperators_stable p v hN w hw)
      have hz := (p.shortNegativeSpan v).add_mem hc (p.coeff_mem_shortNegativeSpan v s (ih A hA))
      simpa only [LinearMap.sub_apply, Module.End.mul_apply, sub_add_cancel,
        List.map_cons, List.prod_cons, w] using hz
  intro A hA w hw
  induction hw using Submodule.span_induction with
  | mem w hw => obtain ⟨l, rfl⟩ := hw; exact hword l A hA
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (p.shortNegativeSpan v).add_mem ihx ihy
  | smul c w hw ih =>
    simpa only [map_smul] using (p.shortNegativeSpan v).smul_mem c ih

private def commutatorRight {B : AlgebraicFactor F} (D : Module.End F B.Space) :
    Module.End F B.Space →ₗ[F] Module.End F B.Space where
  toFun A := A * D - D * A
  map_add' A C := by noncomm_ring
  map_smul' c A := by simp only [smul_mul_assoc, mul_smul_comm, smul_sub, RingHom.id_apply]

/-- Positive stability follows from the stated actual root and Cartan commutators. -/
theorem positive_stable_of_commutators {B : AlgebraicFactor F}
    (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v)
    (hcartanv : ∀ i, cartanOperator p i v ∈ Submodule.span F {v})
    (hroot : ∀ r : PositiveRoot, ∀ s : ShortNegativeRoot,
      p.coeff r.val 1 * p.coeff s.val 1 - p.coeff s.val 1 * p.coeff r.val 1 ∈
        nonnegativeOperators p ⊔ negativeOperators p)
    (hcartan : ∀ i, ∀ s : ShortNegativeRoot,
      cartanOperator p i * p.coeff s.val 1 - p.coeff s.val 1 * cartanOperator p i ∈
        negativeOperators p) :
    ∀ r : F4Chevalley.Root, typeF4RootPairing_base.IsPos r →
      ∀ w ∈ p.shortNegativeSpan v, p.coeff r 1 w ∈ p.shortNegativeSpan v := by
  have hinit : ∀ A ∈ nonnegativeOperators p, A v ∈ p.shortNegativeSpan v := by
    change nonnegativeOperators p ≤ (p.shortNegativeSpan v).comap (LinearMap.applyₗ v)
    apply sup_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨r, rfl⟩
      change p.coeff r.val 1 v ∈ p.shortNegativeSpan v
      rw [p.coeff_one_eq_zero_of_fixed r.val v (hv.2.1 r.val r.property)]
      exact Submodule.zero_mem _
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hvle : Submodule.span F {v} ≤ p.shortNegativeSpan v :=
        Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (p.mem_shortNegativeSpan v))
      exact hvle (hcartanv i)
  have hcomm : ∀ A ∈ nonnegativeOperators p, ∀ s : ShortNegativeRoot,
      A * p.coeff s.val 1 - p.coeff s.val 1 * A ∈ nonnegativeOperators p ⊔ negativeOperators p := by
    intro A hA s
    have hle : nonnegativeOperators p ≤ (nonnegativeOperators p ⊔ negativeOperators p).comap
        (commutatorRight (p.coeff s.val 1)) := by
      apply sup_le
      · apply Submodule.span_le.mpr
        rintro _ ⟨r, rfl⟩
        exact hroot r s
      · apply Submodule.span_le.mpr
        rintro _ ⟨i, rfl⟩
        exact (show negativeOperators p ≤ nonnegativeOperators p ⊔ negativeOperators p from le_sup_right)
          (hcartan i s)
    exact hle hA
  intro r hr
  exact stable_of_triangular_commutators p v (nonnegativeOperators p) hinit hcomm _
    ((show positiveOperators p ≤ nonnegativeOperators p from le_sup_left)
      (Submodule.subset_span ⟨⟨r, hr⟩, rfl⟩))

end NegativeCyclicity.SpanInvariance
end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
