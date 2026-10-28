module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.SourceLayerCoordinateModel

/-!
# Relative-root fiber modules

The lower quotient module supplies the Chevalley-generated adjacent-layer
fiber, and the source coordinate model identifies that whole group with the
finite-dimensional space `RelativeRootFiberCoordinate S`.  A fiber module
therefore carries a `k`-linear equivalence from the canonical coordinates to
its vector space and requires its full abstract `pointEquiv` to be exactly the
composite of the canonical coordinate equivalence with that linear map.  This
global compatibility excludes non-linear additive coordinate twists; the
generator-axis clauses remain as convenient source-specific APIs rather than
as the geometric contract.

The Levi action uses left conjugation, `l * x * l⁻¹`, so the generator clause
has the same orientation as its group homomorphism.  An inverse-indexed theorem
below recovers the legacy formula `l⁻¹ * x * l` without treating that
anti-action as a left action.  Finally, closure induction shows that the fiber
generators span every modeled module.  These data formalize the elementary
coordinate setup preceding GLS3, Theorem 1.14.7; no rationality conclusion,
regular-conjugation witness, or numbered theorem is assumed.
-/

set_option warningAsError false
set_option linter.style.haveILetI false

universe u v

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public structure RelativeRootFiberModule
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) where
  V : Type v
  [addCommGroupV : AddCommGroup V]
  [moduleV : Module k V]
  [finiteDimensionalV : FiniteDimensional k V]
  pointEquiv : relativeRootFiberQuotientSubgroup S ≃* Multiplicative V
  coordinateLinearEquiv : RelativeRootFiberCoordinate S ≃ₗ[k] V
  pointEquiv_coordinate : ∀ q,
    pointEquiv q =
      AddEquiv.toMultiplicative coordinateLinearEquiv.toAddEquiv
        (relativeRootFiberQuotientCoordinateEquiv S q)
  representation : RationalRepresentation S.L.carrierVariety V
  conjugationAction :
    Variety.Point S.L.carrierVariety →*
      MulAut (relativeRootFiberQuotientSubgroup S)
  conjugatedGenerator :
    Variety.Point S.L.carrierVariety →
        ({γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
        S.D S.coeff S.J S.height S.root} × k) →
        relativeRootFiberQuotientSubgroup S
  conjugatedGenerator_value : ∀ l z,
    ∃ y : sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
        S.coeff S.J S.height,
      (y : Variety.Point K) =
          S.L.includePoint l * S.C.x z.1.1 z.2 * (S.L.includePoint l)⁻¹ ∧
        (conjugatedGenerator l z : relativeRootLayerQuotient S) =
          QuotientGroup.mk' _ y
  conjugationAction_generator : ∀ l z,
    conjugationAction l (relativeRootFiberQuotientGenerator S z) =
      conjugatedGenerator l z
  representation_agrees_with_conjugation : ∀ l q,
    pointEquiv (conjugationAction l q) =
      Multiplicative.ofAdd
        ((representation.action l).1
          (Multiplicative.toAdd (pointEquiv q)))
  rootParameterLinear :
    { γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root } → k →ₗ[k] V
  rootParameterLinear_value : ∀ γ t,
    rootParameterLinear γ t = Multiplicative.toAdd
      (pointEquiv (relativeRootFiberQuotientGenerator S (γ, t)))

attribute [instance] RelativeRootFiberModule.addCommGroupV
  RelativeRootFiberModule.moduleV RelativeRootFiberModule.finiteDimensionalV

/-- Inverse conjugation is the repaired left action evaluated at the inverse
Levi point.  This is the compatibility form for proofs whose source calculation
is written as `l⁻¹ * x * l`. -/
public theorem RelativeRootFiberModule.conjugatedGenerator_inv_value
    {K : Variety k} [AlgebraicGroup K]
    {S : RelativeRootRepresentationSource K}
    (M : RelativeRootFiberModule S)
    (l : Variety.Point S.L.carrierVariety)
    (z : {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root} × k) :
    ∃ y : sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
        S.coeff S.J S.height,
      (y : Variety.Point K) =
          (S.L.includePoint l)⁻¹ * S.C.x z.1.1 z.2 * S.L.includePoint l ∧
        (M.conjugatedGenerator l⁻¹ z : relativeRootLayerQuotient S) =
          QuotientGroup.mk' _ y := by
  rcases M.conjugatedGenerator_value l⁻¹ z with ⟨y, hy, hqy⟩
  refine ⟨y, ?_, hqy⟩
  have hinv : S.L.includePoint l⁻¹ = (S.L.includePoint l)⁻¹ := by rfl
  rw [hinv, inv_inv] at hy
  exact hy

public noncomputable def RelativeRootFiberModule.rootVector
    {K : Variety k} [AlgebraicGroup K]
    {S : RelativeRootRepresentationSource K}
    (M : RelativeRootFiberModule S)
    (z : {γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root} × k) : M.V :=
  Multiplicative.toAdd (M.pointEquiv (relativeRootFiberQuotientGenerator S z))

/-- The root-vector map is the additive transport of the quotient generator
through the chosen point equivalence. -/
public theorem RelativeRootFiberModule.rootVector_value
    {K : Variety k} [AlgebraicGroup K]
    {S : RelativeRootRepresentationSource K}
    (M : RelativeRootFiberModule S)
    (z : {γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root} × k) :
    M.rootVector z = Multiplicative.toAdd
      (M.pointEquiv (relativeRootFiberQuotientGenerator S z)) := by
  rfl

/-!
The fiber quotient is generated by all root-layer classes.  Transporting this
closure through `M.pointEquiv` turns multiplication and inversion into
addition and negation, so the corresponding root vectors span `M.V`.
-/
public theorem relativeRootFiberQuotientGenerator_span_eq_top
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (M : RelativeRootFiberModule S) :
    Submodule.span k (Set.range M.rootVector) = ⊤ := by
  letI := relativeRootLayerQuotientGroup S
  apply top_unique
  intro v _
  let q : relativeRootFiberQuotientSubgroup S :=
    M.pointEquiv.symm (Multiplicative.ofAdd v)
  have q_mem : q.1 ∈ Subgroup.closure
      (Set.range fun z :
        {γ : S.D.Root // γ ∈ relativeRootFiberAtHeight S.D S.coeff S.J
          S.height S.root} × k =>
        QuotientGroup.mk' _ (relativeRootLayerElement S z.1.1 z.1.2 z.2)) := by
    rw [← relativeRootFiberQuotientSubgroup_spec S]
    exact q.2
  have hq : Multiplicative.toAdd (M.pointEquiv q) ∈
      Submodule.span k (Set.range M.rootVector) := by
    refine Subgroup.closure_induction
      (p := fun x hx =>
        Multiplicative.toAdd (M.pointEquiv ⟨x, by
          rw [relativeRootFiberQuotientSubgroup_spec S]
          exact hx⟩) ∈ Submodule.span k (Set.range M.rootVector))
      (x := q.1) ?_ ?_ ?_ ?_ q_mem
    · rintro x ⟨z, rfl⟩
      have heq : (⟨QuotientGroup.mk' _
          (relativeRootLayerElement S z.1.1 z.1.2 z.2), by
            rw [relativeRootFiberQuotientSubgroup_spec S]
            exact Subgroup.subset_closure ⟨z, rfl⟩⟩ :
          relativeRootFiberQuotientSubgroup S) =
          relativeRootFiberQuotientGenerator S z := by
        apply Subtype.ext
        exact (relativeRootFiberQuotientGenerator_coe S z).symm
      rw [heq, ← RelativeRootFiberModule.rootVector_value M z]
      exact Submodule.subset_span ⟨z, rfl⟩
    · have heq : (⟨1, by
          rw [relativeRootFiberQuotientSubgroup_spec S]
          exact (Subgroup.closure _).one_mem⟩ :
          relativeRootFiberQuotientSubgroup S) = 1 := by
        apply Subtype.ext
        rfl
      rw [heq, map_one]
      exact (Submodule.span k (Set.range M.rootVector)).zero_mem
    · intro x y hx hy hxW hyW
      have heq : (⟨x * y, by
          rw [relativeRootFiberQuotientSubgroup_spec S]
          exact (Subgroup.closure _).mul_mem hx hy⟩ :
          relativeRootFiberQuotientSubgroup S) =
          ⟨x, by rw [relativeRootFiberQuotientSubgroup_spec S]; exact hx⟩ *
            ⟨y, by rw [relativeRootFiberQuotientSubgroup_spec S]; exact hy⟩ := by
        apply Subtype.ext
        rfl
      rw [heq, map_mul]
      exact (Submodule.span k (Set.range M.rootVector)).add_mem hxW hyW
    · intro x hx hxW
      have heq : (⟨x⁻¹, by
          rw [relativeRootFiberQuotientSubgroup_spec S]
          exact (Subgroup.closure _).inv_mem hx⟩ :
          relativeRootFiberQuotientSubgroup S) =
          (⟨x, by rw [relativeRootFiberQuotientSubgroup_spec S]; exact hx⟩ :
            relativeRootFiberQuotientSubgroup S)⁻¹ := by
        apply Subtype.ext
        rfl
      rw [heq, map_inv]
      exact (Submodule.span k (Set.range M.rootVector)).neg_mem hxW
  simpa [q] using hq

end Theory.AlgebraicGroup
