module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.HighestLine
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft.Generation
/-!
# Triangular commutation for actual D4 coefficients

Induction on negative-word length propagates the initial action of a space of
operators whenever its brackets with negative generators stay in that space
plus the negative generators. Apply this simultaneously to positive and Cartan
operators. The coefficient bracket identities and initial Cartan action are
explicit inputs; no infinitesimal irreducibility is assumed.

The induction follows the F4 `NegativeCyclicity.SpanInvariance.Triangular`
argument, with the actual arbitrary D4 root curves throughout.
Source: Steinberg, *Representations of Algebraic Groups* (1963), §§2 and 4;
GLS3 Theorem 2.8.5 and Corollary 2.8.6(a).
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity
@[expose] public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
namespace NegativeCyclicityLeft

/-- The linear span of all negative first root coefficients. -/
def negativeOperators (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsRationalRepresentation ρ) : Submodule k (Module.End k V) :=
  Submodule.span k (Set.range fun α : PositiveRoot S => rootOperator S ρ hρ (S.roots.neg α.val))
/-- The linear span of all positive first root coefficients. -/
def positiveOperators (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsRationalRepresentation ρ) : Submodule k (Module.End k V) :=
  Submodule.span k (Set.range fun α : PositiveRoot S => rootOperator S ρ hρ α.val)
/-- The actual bracket of a numbered simple root coefficient with its opposite. -/
def cartanOperator (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsRationalRepresentation ρ) (i : Fin 4) : Module.End k V :=
  rootOperator S ρ hρ (simpleRoot S i) * rootOperator S ρ hρ (S.roots.neg (simpleRoot S i)) -
    rootOperator S ρ hρ (S.roots.neg (simpleRoot S i)) * rootOperator S ρ hρ (simpleRoot S i)
/-- The span of the four simple Cartan brackets. -/
def cartanOperators (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsRationalRepresentation ρ) : Submodule k (Module.End k V) :=
  Submodule.span k (Set.range (cartanOperator S ρ hρ))
/-- Positive coefficients together with simple Cartan brackets. -/
def nonnegativeOperators (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsRationalRepresentation ρ) : Submodule k (Module.End k V) :=
  positiveOperators S ρ hρ ⊔ cartanOperators S ρ hρ

/-- The empty negative word contains the initial vector. -/
theorem mem_negativeRootSpan (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsRationalRepresentation ρ) (v : V) : v ∈ negativeRootSpan S ρ hρ v := by
  exact Submodule.subset_span ⟨[], by simp⟩

/-- Prepending a negative coefficient preserves the negative-word span. -/
theorem negative_rootOperator_mem (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsRationalRepresentation ρ) (v : V) (α : PositiveRoot S)
    {w : V} (hw : w ∈ negativeRootSpan S ρ hρ v) :
    rootOperator S ρ hρ (S.roots.neg α.val) w ∈ negativeRootSpan S ρ hρ v := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨l, rfl⟩ := hw
    exact Submodule.subset_span ⟨α :: l, by simp⟩
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (negativeRootSpan S ρ hρ v).add_mem ihx ihy
  | smul c w hw ih =>
    simpa only [map_smul] using (negativeRootSpan S ρ hρ v).smul_mem c ih

/-- Every linear combination of negative coefficients preserves their word span. -/
theorem negativeOperators_stable (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsRationalRepresentation ρ) (v : V) {A : Module.End k V}
    (hA : A ∈ negativeOperators S ρ hρ) :
    ∀ w ∈ negativeRootSpan S ρ hρ v, A w ∈ negativeRootSpan S ρ hρ v := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨α, rfl⟩ := hA
    exact fun _ hw => negative_rootOperator_mem S ρ hρ v α hw
  | zero => simp
  | add A D hA hD ihA ihD =>
    intro w hw
    exact (negativeRootSpan S ρ hρ v).add_mem (ihA w hw) (ihD w hw)
  | smul c A hA ihA =>
    intro w hw
    exact (negativeRootSpan S ρ hρ v).smul_mem c (ihA w hw)

/-- Triangular commutation propagates initial membership along all negative words. -/
theorem stable_of_triangular_commutators (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsRationalRepresentation ρ) (v : V) (L : Submodule k (Module.End k V))
    (hinit : ∀ A ∈ L, A v ∈ negativeRootSpan S ρ hρ v)
    (hcomm : ∀ A ∈ L, ∀ α : PositiveRoot S,
      A * rootOperator S ρ hρ (S.roots.neg α.val) -
        rootOperator S ρ hρ (S.roots.neg α.val) * A ∈ L ⊔ negativeOperators S ρ hρ) :
    ∀ A ∈ L, ∀ w ∈ negativeRootSpan S ρ hρ v, A w ∈ negativeRootSpan S ρ hρ v := by
  have hword (l : List (PositiveRoot S)) : ∀ A ∈ L,
      A ((l.map fun α => rootOperator S ρ hρ (S.roots.neg α.val)).prod v) ∈
        negativeRootSpan S ρ hρ v := by
    induction l with
    | nil => simpa using hinit
    | cons α l ih =>
      intro A hA
      let w := (l.map fun α => rootOperator S ρ hρ (S.roots.neg α.val)).prod v
      have hw : w ∈ negativeRootSpan S ρ hρ v := Submodule.subset_span ⟨l, rfl⟩
      obtain ⟨D, hD, N, hN, he⟩ := Submodule.mem_sup.mp (hcomm A hA α)
      have hc : (A * rootOperator S ρ hρ (S.roots.neg α.val) -
          rootOperator S ρ hρ (S.roots.neg α.val) * A) w ∈ negativeRootSpan S ρ hρ v := by
        rw [← he]
        exact (negativeRootSpan S ρ hρ v).add_mem (ih D hD)
          (negativeOperators_stable S ρ hρ v hN w hw)
      have hz := (negativeRootSpan S ρ hρ v).add_mem hc
        (negative_rootOperator_mem S ρ hρ v α (ih A hA))
      simpa only [LinearMap.sub_apply, Module.End.mul_apply, sub_add_cancel,
        List.map_cons, List.prod_cons, w] using hz
  intro A hA w hw
  induction hw using Submodule.span_induction with
  | mem w hw => obtain ⟨l, rfl⟩ := hw; exact hword l A hA
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (negativeRootSpan S ρ hρ v).add_mem ihx ihy
  | smul c w hw ih =>
    simpa only [map_smul] using (negativeRootSpan S ρ hρ v).smul_mem c ih

private def commutatorRight (D : Module.End k V) :
    Module.End k V →ₗ[k] Module.End k V where
  toFun A := A * D - D * A
  map_add' A C := by noncomm_ring
  map_smul' c A := by simp only [smul_mul_assoc, mul_smul_comm, smul_sub, RingHom.id_apply]

/-- Actual root and Cartan bracket identities imply invariance of the negative-word span. -/
theorem rootOperatorInvariant_of_triangular_commutators (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    {χ : TorusWeight S.torus} {v : V} (hv : HasHighWeight ρ S.borel S.torus v χ)
    (hcartanv : ∀ i, cartanOperator S ρ hρ i v ∈ Submodule.span k {v})
    (hroot : ∀ α β : PositiveRoot S,
      rootOperator S ρ hρ α.val * rootOperator S ρ hρ (S.roots.neg β.val) -
        rootOperator S ρ hρ (S.roots.neg β.val) * rootOperator S ρ hρ α.val ∈
          nonnegativeOperators S ρ hρ ⊔ negativeOperators S ρ hρ)
    (hcartan : ∀ i, ∀ β : PositiveRoot S,
      cartanOperator S ρ hρ i * rootOperator S ρ hρ (S.roots.neg β.val) -
        rootOperator S ρ hρ (S.roots.neg β.val) * cartanOperator S ρ hρ i ∈
          negativeOperators S ρ hρ) :
    IsRootOperatorInvariant S ρ hρ (negativeRootSpan S ρ hρ v) := by
  have hinit : ∀ A ∈ nonnegativeOperators S ρ hρ, A v ∈ negativeRootSpan S ρ hρ v := by
    change nonnegativeOperators S ρ hρ ≤ (negativeRootSpan S ρ hρ v).comap (LinearMap.applyₗ v)
    apply sup_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨α, rfl⟩
      change rootOperator S ρ hρ α.val v ∈ negativeRootSpan S ρ hρ v
      rw [positive_rootOperator_eq_zero_of_highWeight S ρ hρ hv α.val α.property]
      exact Submodule.zero_mem _
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hvle : Submodule.span k {v} ≤ negativeRootSpan S ρ hρ v :=
        Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (mem_negativeRootSpan S ρ hρ v))
      exact hvle (hcartanv i)
  have hcomm : ∀ A ∈ nonnegativeOperators S ρ hρ, ∀ β : PositiveRoot S,
      A * rootOperator S ρ hρ (S.roots.neg β.val) -
        rootOperator S ρ hρ (S.roots.neg β.val) * A ∈
          nonnegativeOperators S ρ hρ ⊔ negativeOperators S ρ hρ := by
    intro A hA β
    have hle : nonnegativeOperators S ρ hρ ≤
        (nonnegativeOperators S ρ hρ ⊔ negativeOperators S ρ hρ).comap
          (commutatorRight (rootOperator S ρ hρ (S.roots.neg β.val))) := by
      apply sup_le
      · apply Submodule.span_le.mpr
        rintro _ ⟨α, rfl⟩
        exact hroot α β
      · apply Submodule.span_le.mpr
        rintro _ ⟨i, rfl⟩
        exact (show negativeOperators S ρ hρ ≤ _ from le_sup_right) (hcartan i β)
    exact hle hA
  have hp (α : PositiveRoot S) :=
    stable_of_triangular_commutators S ρ hρ v _ hinit hcomm (rootOperator S ρ hρ α.val)
      ((show positiveOperators S ρ hρ ≤ nonnegativeOperators S ρ hρ from le_sup_left)
        (Submodule.subset_span ⟨α, rfl⟩))
  intro α w hw
  have hsign : α ∈ S.roots.positive ∨ S.roots.neg α ∈ S.roots.positive := by
    have h := S.bigCell.data.positive.2.1
    exact (Set.ext_iff.mp h α).mpr (Set.mem_univ α)
  rcases hsign with hpos | hneg
  · exact hp ⟨α, hpos⟩ w hw
  · simpa only [S.realized.neg_neg] using
      negative_rootOperator_mem S ρ hρ v ⟨S.roots.neg α, hneg⟩ hw
end NegativeCyclicityLeft
end
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity
