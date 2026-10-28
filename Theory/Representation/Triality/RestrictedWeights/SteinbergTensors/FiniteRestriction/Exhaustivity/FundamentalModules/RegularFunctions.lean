module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.HighestWeightConstruction
public import Theory.AlgebraicGroup.RightTranslation.OrbitRational

/-!
# Fundamental D4 modules from regular highest-weight functions

A regular function fixed by right translation by each positive root subgroup
and transformed by the specified torus character gives a highest vector in its
finite-dimensional rational translation orbit. Its highest vector survives in
an irreducible composition factor. The torus, positive roots, Borel, and weight
coordinates here are exactly those of the supplied geometry.

The remaining geometric construction is the existence of these functions for
the fundamental weights. The construction in this file does not assert that
existence or GLS3 Theorem 1.14.6(e). The separate `OrientationObstruction`
module diagnoses the root/highest-weight convention needed for that assertion.

Sources: GLS3, Definitions 1.14.1--5, Theorem 1.14.6(d)--(e), and Examples
1.14.9(c)--(f). No use is made of the unresolved bundled theorem.
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- A normalized regular function with the actual right highest-weight laws.
These are equations of regular functions on the given group, not assumptions
about existence or irreducibility of a representation. -/
structure IsHighestWeightRegularFunction (S : Geometry K) (a : Weight)
    (f : K.PolynomialFunction) : Prop where
  at_one : f 1 = 1
  torus : ∀ (t : Variety.Point S.torus.carrierVariety) (x : Variety.Point K),
    f (x * S.torus.includePoint t) = (S.coordinateEmbedding a).pointCharacter t * f x
  positive_root : ∀ r ∈ S.roots.positive,
    ∀ (v : Variety.Point (S.roots.rootSubgroup r).carrierVariety) (x : Variety.Point K),
      f (x * (S.roots.rootSubgroup r).includePoint v) = f x

omit [IsAlgClosed k] in
/-- The positive-root equations extend to the subgroup those roots generate. -/
theorem IsHighestWeightRegularFunction.positive_generated
    {S : Geometry K} {a : Weight} {f : K.PolynomialFunction}
    (hf : IsHighestWeightRegularFunction S a f)
    (v : Variety.Point K) (hv : v ∈ RootSubgroupGenerated S.roots S.roots.positive)
    (x : Variety.Point K) : f (x * v) = f x := by
  let H : Subgroup (Variety.Point K) := {
    carrier := {g | ∀ x, f (x * g) = f x}
    one_mem' := by intro x; rw [mul_one]
    mul_mem' := by
      intro g h hg hh x
      rw [← mul_assoc, hh, hg]
    inv_mem' := by
      intro g hg x
      have h := hg (x * g⁻¹)
      simpa only [inv_mul_cancel_right] using h.symm }
  have hle : RootSubgroupGenerated S.roots S.roots.positive ≤ H := by
    apply (Subgroup.closure_le H).2
    intro g hg
    obtain ⟨r, hr, hg⟩ := Set.mem_iUnion₂.mp hg
    intro y
    let w := (S.roots.rootSubgroup r).pointEquiv.symm ⟨g, hg⟩
    have hw : (S.roots.rootSubgroup r).includePoint w = g := by
      exact congrArg Subtype.val ((S.roots.rootSubgroup r).pointEquiv.apply_symm_apply ⟨g, hg⟩)
    rw [← hw]
    exact hf.positive_root r hr w y
  exact hle hv x

/-- A normalized regular highest-weight function constructs a nonzero rational
irreducible with that highest weight, through its finite translation orbit. -/
theorem rationalFactor_exists_of_regularFunction (S : Geometry K) {a : Weight}
    (f : K.PolynomialFunction) (hf : IsHighestWeightRegularFunction S a f) :
    ∃ A : RationalFactor K, HasHighestWeight S A a := by
  let ρ := rightTranslateOrbitRationalRepresentation K f
  have hmem : f ∈ rightTranslateOrbitSpan K f :=
    Submodule.subset_span ⟨1, rightMul_pullback_one K f⟩
  let v : rightTranslateOrbitSpan K f := ⟨f, hmem⟩
  have hv : v ≠ 0 := by
    intro h
    have hzero := congrArg (fun q : rightTranslateOrbitSpan K f => q.val 1) h
    change f 1 = 0 at hzero
    rw [hf.at_one] at hzero
    exact one_ne_zero hzero
  apply rationalFactor_exists_of_highWeight S ρ
    (rightTranslateOrbitRationalRepresentation_isRational K f) v
  refine ⟨⟨hv, ?_⟩, hv, ?_⟩
  · intro b hb
    obtain ⟨t, w, ht, hw, rfl⟩ := (S.bigCell.positive_decomposition b).mp hb
    let t' := S.torus.pointEquiv.symm ⟨t, ht⟩
    have ht' : S.torus.includePoint t' = t :=
      congrArg Subtype.val (S.torus.pointEquiv.apply_symm_apply ⟨t, ht⟩)
    refine ⟨(S.coordinateEmbedding a).pointCharacter t', ?_⟩
    apply Subtype.ext
    apply Variety.PolynomialFunction.ext
    intro x
    change (((rightTranslateOrbitRationalRepresentation K f).action (t * w)).1 v).val x = _
    rw [rightTranslateOrbitRationalRepresentation_apply]
    change f (x * (t * w)) = _
    rw [← mul_assoc, hf.positive_generated w hw, ← ht', hf.torus]
    exact (polynomialFunction_smul_apply K _ f x).symm
  · intro t
    apply Subtype.ext
    apply Variety.PolynomialFunction.ext
    intro x
    change (((rightTranslateOrbitRationalRepresentation K f).action
      (S.torus.includePoint t)).1 v).val x = _
    rw [rightTranslateOrbitRationalRepresentation_apply]
    change f (x * S.torus.includePoint t) = _
    rw [hf.torus]
    exact (polynomialFunction_smul_apply K _ f x).symm


end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
