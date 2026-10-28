module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.RepresentationSourceCoordinateEquivalence

/-!
# Source relative-root fiber coordinates

For a representation source `S`, this module identifies its actual adjacent
relative-root fiber quotient with the multiplicative form of a finite-dimensional
space of exact-height root coordinates.  Commutativity and coordinate
independence come from the exact-layer coordinate equivalence; surjectivity is
proved directly from the defining subgroup closure.  Thus no classification or
later relative-root representation theorem enters the construction.  These
coordinates are the elementary quotient model used in the representation
construction following GLS3, Section 1.14.
-/

universe u

namespace Theory.AlgebraicGroup

open scoped BigOperators IsMulCommutative

set_option linter.style.haveILetI false

variable {k : Type u} [Field k] [IsAlgClosed k]

public abbrev RelativeRootFiberCoordinate
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :=
  {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
    S.D S.coeff S.J S.height S.root} → k

noncomputable instance
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    FiniteDimensional k (RelativeRootFiberCoordinate S) := by
  letI : Finite {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root} := by infer_instance
  letI := Fintype.ofFinite {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root}
  infer_instance

/-- Extend fiber coordinates by zero to all roots of the source's exact height. -/
public noncomputable def relativeRootFiberCoordinateExtension
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    RelativeRootFiberCoordinate S →ₗ[k]
      ({gamma : S.D.Root //
        RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
          S.height} → k) where
  toFun a eta := by
    classical
    exact if h : eta.1 ∈ relativeRootFiberAtHeight
        S.D S.coeff S.J S.height S.root then a ⟨eta.1, h⟩ else 0
  map_add' a b := by
    funext eta
    by_cases h : eta.1 ∈ relativeRootFiberAtHeight
        S.D S.coeff S.J S.height S.root <;> simp [h]
  map_smul' c a := by
    funext eta
    by_cases h : eta.1 ∈ relativeRootFiberAtHeight
        S.D S.coeff S.J S.height S.root <;> simp [h]

omit [IsAlgClosed k] in
/-- Extension by zero retains a coordinate whose root lies in the fiber. -/
public theorem relativeRootFiberCoordinateExtension_apply_of_mem
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (a : RelativeRootFiberCoordinate S)
    (eta : {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height})
    (heta : eta.1 ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root) :
    relativeRootFiberCoordinateExtension S a eta = a ⟨eta.1, heta⟩ := by
  simp [relativeRootFiberCoordinateExtension, heta]

omit [IsAlgClosed k] in
/-- Extension by zero vanishes away from the selected relative-root fiber. -/
public theorem relativeRootFiberCoordinateExtension_apply_of_not_mem
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (a : RelativeRootFiberCoordinate S)
    (eta : {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height})
    (heta : eta.1 ∉ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root) :
    relativeRootFiberCoordinateExtension S a eta = 0 := by
  simp [relativeRootFiberCoordinateExtension, heta]

private theorem relativeRootFiberQuotientGenerator_zero
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root}) :
    relativeRootFiberQuotientGenerator S (gamma, 0) = 1 := by
  apply Subtype.ext
  apply (relativeRootLayerQuotient_coordinateEquiv S).injective
  rw [relativeRootFiberQuotientGenerator_coe]
  have helem : relativeRootLayerElement S gamma.1 gamma.2 0 =
      relativeRootLayerExactElement S ⟨gamma.1, gamma.2.2⟩ 0 := by
    apply Subtype.ext
    rw [relativeRootLayerElement_coe, relativeRootLayerExactElement_value]
  rw [helem]
  simpa using relativeRootLayerQuotient_coordinateEquiv_root S
    ⟨gamma.1, gamma.2.2⟩ 0

private theorem relativeRootFiberQuotientGenerator_add
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root}) (a b : k) :
    relativeRootFiberQuotientGenerator S (gamma, a + b) =
      relativeRootFiberQuotientGenerator S (gamma, a) *
        relativeRootFiberQuotientGenerator S (gamma, b) := by
  classical
  letI : DecidableEq {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} := Classical.decEq _
  have hcoord (t : k) :
      relativeRootLayerQuotient_coordinateEquiv S
          (relativeRootFiberQuotientGenerator S (gamma, t) :
            relativeRootLayerQuotient S) =
        Multiplicative.ofAdd (Pi.single ⟨gamma.1, gamma.2.2⟩ t) := by
    rw [relativeRootFiberQuotientGenerator_coe]
    have helem : relativeRootLayerElement S gamma.1 gamma.2 t =
        relativeRootLayerExactElement S ⟨gamma.1, gamma.2.2⟩ t := by
      apply Subtype.ext
      rw [relativeRootLayerElement_coe, relativeRootLayerExactElement_value]
    rw [helem]
    exact relativeRootLayerQuotient_coordinateEquiv_root S ⟨gamma.1, gamma.2.2⟩ t
  apply Subtype.ext
  apply (relativeRootLayerQuotient_coordinateEquiv S).injective
  rw [Subgroup.coe_mul, map_mul, hcoord, hcoord, hcoord]
  let egamma : {gamma : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J gamma =
        S.height} := ⟨gamma.1, gamma.2.2⟩
  change (Pi.single egamma (a + b) : _ → k) =
    (Pi.single egamma a : _ → k) + (Pi.single egamma b : _ → k)
  funext x
  by_cases hx : x = egamma
  · subst x
    simp
  · simp [Pi.single, hx]

public noncomputable def relativeRootFiberCoordinateHom
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    Multiplicative (RelativeRootFiberCoordinate S) →*
      relativeRootFiberQuotientSubgroup S := by
  letI : Finite {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root} := by infer_instance
  letI := Fintype.ofFinite {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root}
  letI : IsMulCommutative (relativeRootLayerQuotient S) :=
    relativeRootLayerQuotient_commutative S
  exact {
    toFun := fun a => ∏ gamma,
      relativeRootFiberQuotientGenerator S (gamma, a.toAdd gamma)
    map_one' := by simp [relativeRootFiberQuotientGenerator_zero]
    map_mul' := by
      intro a b
      change (∏ gamma, relativeRootFiberQuotientGenerator S
        (gamma, a.toAdd gamma + b.toAdd gamma)) = _
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro gamma _
      exact relativeRootFiberQuotientGenerator_add S gamma _ _
  }

public theorem relativeRootFiberCoordinateHom_single
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root}) (t : k) :
    letI : DecidableEq {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root} := Classical.decEq _
    relativeRootFiberCoordinateHom S
        (Multiplicative.ofAdd
          (show RelativeRootFiberCoordinate S from Pi.single gamma t)) =
      relativeRootFiberQuotientGenerator S (gamma, t) := by
  letI : Finite {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root} := by infer_instance
  letI := Fintype.ofFinite {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root}
  letI : IsMulCommutative (relativeRootLayerQuotient S) :=
    relativeRootLayerQuotient_commutative S
  classical
  letI : DecidableEq {root : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J root =
        S.height} := Classical.decEq _
  unfold relativeRootFiberCoordinateHom
  dsimp
  rw [Fintype.prod_eq_single gamma]
  · simp
  · intro x hx
    simp [Pi.single, hx, relativeRootFiberQuotientGenerator_zero]

/-- In ambient exact-height coordinates, the fiber homomorphism is extension
by zero from the selected relative-root fiber. -/
public theorem relativeRootFiberCoordinateHom_coordinates
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (a : Multiplicative (RelativeRootFiberCoordinate S)) :
    Multiplicative.toAdd
        (relativeRootLayerQuotient_coordinateEquiv S
          ((relativeRootFiberCoordinateHom S a :
            relativeRootFiberQuotientSubgroup S) : relativeRootLayerQuotient S)) =
      relativeRootFiberCoordinateExtension S a.toAdd := by
  letI : Finite {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root} := by infer_instance
  letI := Fintype.ofFinite {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root}
  letI : IsMulCommutative (relativeRootLayerQuotient S) :=
    relativeRootLayerQuotient_commutative S
  classical
  letI : DecidableEq {root : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J root =
        S.height} := Classical.decEq _
  have hcoe :
      ((relativeRootFiberCoordinateHom S a :
          relativeRootFiberQuotientSubgroup S) : relativeRootLayerQuotient S) =
        ∏ delta, (relativeRootFiberQuotientGenerator S
          (delta, a.toAdd delta) : relativeRootLayerQuotient S) := by
    unfold relativeRootFiberCoordinateHom
    dsimp
    exact map_prod (Subgroup.subtype (relativeRootFiberQuotientSubgroup S)) _ _
  rw [hcoe, map_prod]
  have hcoord (delta : {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root}) :
      relativeRootLayerQuotient_coordinateEquiv S
          (relativeRootFiberQuotientGenerator S (delta, a.toAdd delta) :
            relativeRootLayerQuotient S) =
        Multiplicative.ofAdd
          (Pi.single ⟨delta.1, delta.2.2⟩ (a.toAdd delta)) := by
    rw [relativeRootFiberQuotientGenerator_coe]
    have helem : relativeRootLayerElement S delta.1 delta.2 (a.toAdd delta) =
        relativeRootLayerExactElement S ⟨delta.1, delta.2.2⟩ (a.toAdd delta) := by
      apply Subtype.ext
      rw [relativeRootLayerElement_coe, relativeRootLayerExactElement_value]
    rw [helem]
    simpa only using relativeRootLayerQuotient_coordinateEquiv_root S
      ⟨delta.1, delta.2.2⟩ (a.toAdd delta)
  simp_rw [hcoord]
  change (∑ delta, (Pi.single
      (⟨delta.1, delta.2.2⟩ : {root : S.D.Root //
        RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J root =
          S.height}) (a.toAdd delta) :
        {root : S.D.Root //
          RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J root =
            S.height} → k)) = relativeRootFiberCoordinateExtension S a.toAdd
  funext eta
  simp only [Finset.sum_apply]
  by_cases heta : eta.1 ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root
  · let gamma : {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
        S.D S.coeff S.J S.height S.root} := ⟨eta.1, heta⟩
    rw [Fintype.sum_eq_single gamma]
    · rw [relativeRootFiberCoordinateExtension_apply_of_mem S a.toAdd eta heta]
      simp [gamma]
    · intro delta hne
      have hne' : (⟨delta.1, delta.2.2⟩ : {root : S.D.Root //
          RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J root =
            S.height}) ≠ eta := by
        intro h
        apply hne
        apply Subtype.ext
        change delta.1 = eta.1
        exact congrArg Subtype.val h
      exact Pi.single_eq_of_ne hne'.symm _
  · rw [relativeRootFiberCoordinateExtension_apply_of_not_mem S a.toAdd eta heta]
    apply Finset.sum_eq_zero
    intro delta _
    have hne : (⟨delta.1, delta.2.2⟩ : {root : S.D.Root //
        RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J root =
          S.height}) ≠ eta := by
      intro h
      apply heta
      have hval : delta.1 = eta.1 := congrArg Subtype.val h
      exact hval ▸ delta.2
    exact Pi.single_eq_of_ne hne.symm _

/-- Exact-height fiber coordinates are independent in the adjacent quotient. -/
public theorem relativeRootFiberCoordinateHom_injective
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    Function.Injective (relativeRootFiberCoordinateHom S) := by
  intro a b hab
  change a.toAdd = b.toAdd
  funext gamma
  let eta : {root : S.D.Root //
      RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J root =
        S.height} := ⟨gamma.1, gamma.2.2⟩
  rw [← relativeRootFiberCoordinateExtension_apply_of_mem S a.toAdd eta gamma.2,
    ← relativeRootFiberCoordinateExtension_apply_of_mem S b.toAdd eta gamma.2,
    ← congrFun (relativeRootFiberCoordinateHom_coordinates S a) eta,
    ← congrFun (relativeRootFiberCoordinateHom_coordinates S b) eta, hab]

/-- The coordinate kernel is stable under scalar multiplication. -/
public theorem relativeRootFiberCoordinateHom_kernel_smul_mem
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (c : k) (a : RelativeRootFiberCoordinate S)
    (ha : relativeRootFiberCoordinateHom S (Multiplicative.ofAdd a) = 1) :
    relativeRootFiberCoordinateHom S (Multiplicative.ofAdd (c • a)) = 1 := by
  have hzero : (Multiplicative.ofAdd a) = 1 :=
    relativeRootFiberCoordinateHom_injective S (by simpa using ha)
  have : a = 0 := congrArg Multiplicative.toAdd hzero
  subst a
  simp

/-- The fiber subgroup is exhausted by its finite exact-height coordinates. -/
public theorem relativeRootFiberCoordinateHom_surjective
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    Function.Surjective (relativeRootFiberCoordinateHom S) := by
  intro q
  have q_mem : q.1 ∈ Subgroup.closure
      (Set.range fun z :
        {γ : S.D.Root // γ ∈ relativeRootFiberAtHeight S.D S.coeff S.J
          S.height S.root} × k =>
        QuotientGroup.mk' _ (relativeRootLayerElement S z.1.1 z.1.2 z.2)) := by
    rw [← relativeRootFiberQuotientSubgroup_spec S]
    exact q.2
  refine Subgroup.closure_induction
    (p := fun x hx => ∃ a, relativeRootFiberCoordinateHom S a =
      (⟨x, by rw [relativeRootFiberQuotientSubgroup_spec S]; exact hx⟩ :
        relativeRootFiberQuotientSubgroup S))
    (x := q.1) ?_ ?_ ?_ ?_ q_mem
  · rintro x ⟨z, rfl⟩
    rcases z with ⟨gamma, t⟩
    classical
    letI : DecidableEq {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
        S.D S.coeff S.J S.height S.root} := Classical.decEq _
    refine ⟨Multiplicative.ofAdd
      (show RelativeRootFiberCoordinate S from Pi.single gamma t), ?_⟩
    have heq : (⟨QuotientGroup.mk' _
        (relativeRootLayerElement S gamma.1 gamma.2 t), by
          rw [relativeRootFiberQuotientSubgroup_spec S]
          exact Subgroup.subset_closure ⟨(gamma, t), rfl⟩⟩ :
        relativeRootFiberQuotientSubgroup S) =
        relativeRootFiberQuotientGenerator S (gamma, t) := by
      apply Subtype.ext
      exact (relativeRootFiberQuotientGenerator_coe S (gamma, t)).symm
    rw [heq]
    exact relativeRootFiberCoordinateHom_single S gamma t
  · refine ⟨1, ?_⟩
    change relativeRootFiberCoordinateHom S 1 = 1
    exact map_one _
  · rintro x y hx hy ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    rw [map_mul, ha, hb]
    rfl
  · rintro x hx ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    rw [map_inv, ha]
    rfl

/-- The actual adjacent fiber quotient is the multiplicative additive coordinate space. -/
public noncomputable def relativeRootFiberQuotientCoordinateEquiv
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    relativeRootFiberQuotientSubgroup S ≃*
      Multiplicative (RelativeRootFiberCoordinate S) :=
  (MulEquiv.ofBijective (relativeRootFiberCoordinateHom S)
    ⟨relativeRootFiberCoordinateHom_injective S,
      relativeRootFiberCoordinateHom_surjective S⟩).symm

/-- Applying the coordinate homomorphism after its inverse equivalence recovers
the original fiber-quotient element. -/
public theorem relativeRootFiberCoordinateHom_equiv_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (q : relativeRootFiberQuotientSubgroup S) :
    relativeRootFiberCoordinateHom S
        (relativeRootFiberQuotientCoordinateEquiv S q) = q := by
  unfold relativeRootFiberQuotientCoordinateEquiv
  exact (MulEquiv.ofBijective (relativeRootFiberCoordinateHom S)
    ⟨relativeRootFiberCoordinateHom_injective S,
      relativeRootFiberCoordinateHom_surjective S⟩).apply_symm_apply q

end Theory.AlgebraicGroup
