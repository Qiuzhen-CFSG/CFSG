module

public import Theory.SpecificGroups.LieType.ProperParabolicFixedRadical.OrbitProduct
public import Theory.SpecificGroups.LieType.ProperParabolicFixedRadical.RootCount
public import Theory.SpecificGroups.LieType.ProperParabolicFixedRadical.Parameters
public import Theory.SpecificGroups.LieType.FiniteParabolicRealization

/-!
# Fixed elements in standard parabolic radicals

These conditional constructions use the actual positive roots outside the Levi
subsystem. A nonidentity periodic element in one absolute root subgroup gives
an element fixed by sigma after multiplication around a commuting root orbit.
Unique ordered coordinates prevent cancellation. Two constructions of the
periodic seed are supplied: the proved root fixed-point count from a genuine
Frobenius-level witness, and a direct calculation from the root-parameter
power formulas with positive accumulated exponent.

Both constructions are applied to `O^{p'}(K^sigma)` through
`restrict_ne_bot_of_fixed_unipotent`, rather than replacing the source group
by the full fixed-point group.

The algebraic radical identification and the source-level choice of an outside
root orbit with the stated properties remain explicit. A whole relative root
group can be nonabelian; these theorems only ask for commutation inside the
chosen absolute orbit. They do not assert that every nonabelian relative block
has already been treated. The source existence and selection of the required
orbit or fixed relative block, including Suzuki–Ree cases, remain necessary
for the theorem for every proper invariant parabolic.

Source: GLS3, Chapter 1, 1.13.1–1.13.3; Chapter 2, §§2.1, 2.3–2.4 and
2.6.4–2.6.5. No implication from arbitrary unipotent Steinberg endomorphisms
or from the unresolved `Lang.theorem_2_1_11` is used.
-/

namespace Theory.AlgebraicGroup.ProperParabolicFixedRadical

variable {k : Type*} [Field k] [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K]
    {p : ℕ} [Fact p.Prime] [CharP k p]

omit [IsAlgClosed k] [Fact p.Prime] [CharP k p] in
/-- Exact root-subgroup transport iterates along the root permutation. -/
public theorem root_orbit_image {T : ClosedSubgroup K} (D : RootGroupData K T)
    (σ : AlgebraicEndomorphism K) (r : Equiv.Perm D.Root)
    (himage : ∀ α, σ.onPoints '' (D.rootSubgroup α : Set (Variety.Point K)) =
      (D.rootSubgroup (r α) : Set (Variety.Point K)))
    (α : D.Root) (n : ℕ) :
    (σ.onPoints^[n]) '' (D.rootSubgroup α : Set (Variety.Point K)) =
      (D.rootSubgroup ((r ^ n) α) : Set (Variety.Point K)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (σ.onPoints^[n + 1]) '' (D.rootSubgroup α : Set (Variety.Point K)) =
          σ.onPoints '' ((σ.onPoints^[n]) ''
            (D.rootSubgroup α : Set (Variety.Point K))) := by
        rw [Set.image_image]
        exact congrArg (fun f : Variety.Point K → Variety.Point K =>
          f '' (D.rootSubgroup α : Set (Variety.Point K)))
            (Function.iterate_succ' (f := σ.onPoints) n)
      _ = (D.rootSubgroup ((r ^ (n + 1)) α) : Set (Variety.Point K)) := by
        rw [ih, himage, pow_succ', Equiv.Perm.mul_apply]

omit [IsAlgClosed k] [Fact p.Prime] [CharP k p] in
/-- Every factor lies among the actual positive roots outside the Levi, so
the orbit product belongs to the literal standard unipotent root factor. -/
public theorem orbitProduct_mem_standardUnipotentRootFactor
    {T : ClosedSubgroup K} (D : RootGroupData K T)
    (σ : AlgebraicEndomorphism K) (r : Equiv.Perm D.Root)
    (himage : ∀ α, σ.onPoints '' (D.rootSubgroup α : Set (Variety.Point K)) =
      (D.rootSubgroup (r α) : Set (Variety.Point K)))
    (positiveRoots sigmaJ : Set D.Root) (α : D.Root) (m : ℕ)
    (houtside : ∀ i < m, (r ^ i) α ∈ positiveRoots \ sigmaJ)
    (x : Variety.Point K) (hx : x ∈ D.rootSubgroup α) :
    orbitProduct σ.onPoints m x ∈ standardUnipotentRootFactor D positiveRoots sigmaJ := by
  apply orbitProduct_mem
  intro i hi
  apply rootSubgroup_le_RootSubgroupGenerated D (houtside i hi)
  have hmem : (σ.onPoints^[i]) x ∈
      (σ.onPoints^[i]) '' (D.rootSubgroup α : Set (Variety.Point K)) :=
    ⟨x, hx, rfl⟩
  rwa [root_orbit_image D σ r himage α i] at hmem

/-- Construct a nonidentity sigma-fixed radical point from an absolute root
orbit with unique commuting coordinates. The periodic seed comes from the
proved root fixed-point count using an actual Frobenius-level witness. -/
public theorem exists_fixed_radical_of_commuting_root_orbit
    {T : ClosedSubgroup K} (D : RootGroupData K T)
    (σ : AlgebraicEndomorphism K) (q : NNReal)
    (hσ : IsFrobeniusEndomorphismOfLevel (r := p) q σ)
    (r : Equiv.Perm D.Root)
    (himage : ∀ α, σ.onPoints '' (D.rootSubgroup α : Set (Variety.Point K)) =
      (D.rootSubgroup (r α) : Set (Variety.Point K)))
    (positiveRoots sigmaJ : Set D.Root) (U : ClosedSubgroup K)
    (hUroots : U.toSubgroup = standardUnipotentRootFactor D positiveRoots sigmaJ)
    (α : D.Root) (hα : IsTorusRootSubgroup T (D.rootSubgroup α))
    (m : ℕ) (hm : 0 < m) (hperiod : (r ^ m) α = α)
    (houtside : ∀ i < m, (r ^ i) α ∈ positiveRoots \ sigmaJ)
    (hcomm : ∀ i < m, ∀ x ∈ D.rootSubgroup α,
      ∀ y ∈ D.rootSubgroup ((r ^ i) α), Commute x y)
    (hcoords : Function.Injective (Subgroup.orderedProduct
      (fun i : Fin m => (D.rootSubgroup ((r ^ i.val) α)).toSubgroup))) :
    ∃ x : Variety.Point K, x ∈ U ∧ σ.onPoints x = x ∧ x ≠ 1 := by
  have hreturn : (σ.onPoints^[m]) ''
      (D.rootSubgroup α : Set (Variety.Point K)) =
      (D.rootSubgroup α : Set (Variety.Point K)) := by
    rw [root_orbit_image D σ r himage α m, hperiod]
  have hmaps : Set.MapsTo (σ.onPoints^[m])
      (D.rootSubgroup α : Set (Variety.Point K))
      (D.rootSubgroup α : Set (Variety.Point K)) := by
    intro x hx
    rw [← hreturn]
    exact ⟨x, hx, rfl⟩
  have hsurj : Set.SurjOn (σ.onPoints^[m])
      (D.rootSubgroup α : Set (Variety.Point K))
      (D.rootSubgroup α : Set (Variety.Point K)) := by
    intro x hx
    rw [← hreturn] at hx
    exact hx
  obtain ⟨x, hx, hfix, hne⟩ :=
    exists_nonidentity_fixed_root_iterate σ q hσ T (D.rootSubgroup α) hα m hm
      hmaps hsurj
  have hmem (i : ℕ) : (σ.onPoints^[i]) x ∈ D.rootSubgroup ((r ^ i) α) := by
    have h : (σ.onPoints^[i]) x ∈
        (σ.onPoints^[i]) '' (D.rootSubgroup α : Set (Variety.Point K)) := ⟨x, hx, rfl⟩
    rwa [root_orbit_image D σ r himage α i] at h
  refine ⟨orbitProduct σ.onPoints m x, ?_, ?_, ?_⟩
  · change orbitProduct σ.onPoints m x ∈ U.toSubgroup
    rw [hUroots]
    exact orbitProduct_mem_standardUnipotentRootFactor D σ r himage
      positiveRoots sigmaJ α m houtside x hx
  · exact orbitProduct_fixed σ.onPoints m x hfix
      (fun i hi => hcomm i hi x hx _ (hmem i))
  · exact orbitProduct_ne_one σ.onPoints m hm _ hcoords x (fun i => hmem i) hne

/-- The orbit witness survives in the actual prime-to-p residual. This
discharges the fixed-element premise of the finite-parabolic transfer theorem. -/
public theorem restrict_ne_bot_of_commuting_root_orbit
    {T : ClosedSubgroup K} (D : RootGroupData K T)
    (σ : AlgebraicEndomorphism K) (q : NNReal)
    (hσ : IsFrobeniusEndomorphismOfLevel (r := p) q σ)
    (r : Equiv.Perm D.Root)
    (himage : ∀ α, σ.onPoints '' (D.rootSubgroup α : Set (Variety.Point K)) =
      (D.rootSubgroup (r α) : Set (Variety.Point K)))
    (positiveRoots sigmaJ : Set D.Root) (U : ClosedSubgroup K)
    (hUroots : U.toSubgroup = standardUnipotentRootFactor D positiveRoots sigmaJ)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (α : D.Root) (hα : IsTorusRootSubgroup T (D.rootSubgroup α))
    (m : ℕ) (hm : 0 < m) (hperiod : (r ^ m) α = α)
    (houtside : ∀ i < m, (r ^ i) α ∈ positiveRoots \ sigmaJ)
    (hcomm : ∀ i < m, ∀ x ∈ D.rootSubgroup α,
      ∀ y ∈ D.rootSubgroup ((r ^ i) α), Commute x y)
    (hcoords : Function.Injective (Subgroup.orderedProduct
      (fun i : Fin m => (D.rootSubgroup ((r ^ i.val) α)).toSubgroup))) :
    FiniteParabolicRealization.restrict σ p U.toSubgroup ≠ ⊥ := by
  obtain ⟨x, hx, hfix, hne⟩ := exists_fixed_radical_of_commuting_root_orbit
    D σ q hσ r himage positiveRoots sigmaJ U hUroots α hα m hm hperiod
      houtside hcomm hcoords
  exact FiniteParabolicRealization.restrict_ne_bot_of_fixed_unipotent
    σ p U hU x hx hfix hne

end Theory.AlgebraicGroup.ProperParabolicFixedRadical

namespace Theory.AlgebraicGroup.ProperParabolicFixedRadical

open scoped BigOperators

variable {k : Type*} [Field k] [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K]
    {p : ℕ} [Fact p.Prime] [CharP k p]

omit [CharP k p] in
/-- Construct the fixed radical point directly from source root-parameter
formulas. The exponent premise is over the common permutation period, as in
`positive_root_orbit_exponent_sum_pos`; the product uses the chosen root orbit.
No ambient Frobenius-level witness is required for this route. -/
public theorem exists_fixed_radical_of_power_parameters
    {T : ClosedSubgroup K} (D : RootGroupData K T)
    (σ : AlgebraicEndomorphism K) (r : Equiv.Perm D.Root)
    (x : D.Root → k → Variety.Point K)
    (hx : ∀ α t, x α t ∈ D.rootSubgroup α)
    (c : D.Root → k) (e : D.Root → ℕ) (hc : ∀ α, c α ≠ 0)
    (hstep : ∀ α t, σ.onPoints (x α t) = x (r α) (c α * t ^ (p ^ e α)))
    (positiveRoots sigmaJ : Set D.Root) (U : ClosedSubgroup K)
    (hUroots : U.toSubgroup = standardUnipotentRootFactor D positiveRoots sigmaJ)
    (α : D.Root) (hparam : Function.Injective (x α)) (hzero : x α 0 = 1)
    (m : ℕ) (hm : 0 < m) (hperiod : (r ^ m) α = α)
    (hexponent : 0 < ∑ i ∈ Finset.range (orderOf r), e ((r ^ i) α))
    (houtside : ∀ i < m, (r ^ i) α ∈ positiveRoots \ sigmaJ)
    (hcomm : ∀ i < m, ∀ a ∈ D.rootSubgroup α,
      ∀ b ∈ D.rootSubgroup ((r ^ i) α), Commute a b)
    (hcoords : Function.Injective (Subgroup.orderedProduct
      (fun i : Fin m => (D.rootSubgroup ((r ^ i.val) α)).toSubgroup))) :
    ∃ y : Variety.Point K, y ∈ U ∧ σ.onPoints y = y ∧ y ≠ 1 := by
  obtain ⟨t, ht, hperiodic⟩ := exists_nonzero_periodic_root_parameter
    σ.onPoints x r p (Fact.out : p.Prime).one_lt c e hc hstep α m hperiod
      (orbit_exponent_sum_pos_of_period r e α m hm hperiod (orderOf r) hexponent)
  have hne : x α t ≠ 1 := by
    intro hone
    exact ht (hparam (hone.trans hzero.symm))
  have hmem (i : ℕ) : (σ.onPoints^[i]) (x α t) ∈ D.rootSubgroup ((r ^ i) α) := by
    obtain ⟨a, _, hiter⟩ := iterate_root_power_parameters σ.onPoints x r p c e hc hstep α i
    rw [hiter]
    exact hx _ _
  refine ⟨orbitProduct σ.onPoints m (x α t), ?_, ?_, ?_⟩
  · change orbitProduct σ.onPoints m (x α t) ∈ U.toSubgroup
    rw [hUroots]
    apply orbitProduct_mem
    intro i hi
    exact rootSubgroup_le_RootSubgroupGenerated D (houtside i hi) (hmem i)
  · exact orbitProduct_fixed σ.onPoints m (x α t) hperiodic
      (fun i hi => hcomm i hi _ (hx α t) _ (hmem i))
  · exact orbitProduct_ne_one σ.onPoints m hm _ hcoords (x α t)
      (fun i => hmem i) hne

/-- Apply the parameter construction to the actual prime-to-p residual. The
unipotence premise is precisely what places all fixed radical points there. -/
public theorem restrict_ne_bot_of_power_parameters
    {T : ClosedSubgroup K} (D : RootGroupData K T)
    (σ : AlgebraicEndomorphism K) (r : Equiv.Perm D.Root)
    (x : D.Root → k → Variety.Point K)
    (hx : ∀ α t, x α t ∈ D.rootSubgroup α)
    (c : D.Root → k) (e : D.Root → ℕ) (hc : ∀ α, c α ≠ 0)
    (hstep : ∀ α t, σ.onPoints (x α t) = x (r α) (c α * t ^ (p ^ e α)))
    (positiveRoots sigmaJ : Set D.Root) (U : ClosedSubgroup K)
    (hUroots : U.toSubgroup = standardUnipotentRootFactor D positiveRoots sigmaJ)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (α : D.Root) (hparam : Function.Injective (x α)) (hzero : x α 0 = 1)
    (m : ℕ) (hm : 0 < m) (hperiod : (r ^ m) α = α)
    (hexponent : 0 < ∑ i ∈ Finset.range (orderOf r), e ((r ^ i) α))
    (houtside : ∀ i < m, (r ^ i) α ∈ positiveRoots \ sigmaJ)
    (hcomm : ∀ i < m, ∀ a ∈ D.rootSubgroup α,
      ∀ b ∈ D.rootSubgroup ((r ^ i) α), Commute a b)
    (hcoords : Function.Injective (Subgroup.orderedProduct
      (fun i : Fin m => (D.rootSubgroup ((r ^ i.val) α)).toSubgroup))) :
    FiniteParabolicRealization.restrict σ p U.toSubgroup ≠ ⊥ := by
  obtain ⟨y, hy, hfix, hne⟩ := exists_fixed_radical_of_power_parameters
    D σ r x hx c e hc hstep positiveRoots sigmaJ U hUroots α hparam hzero
      m hm hperiod hexponent houtside hcomm hcoords
  exact FiniteParabolicRealization.restrict_ne_bot_of_fixed_unipotent
    σ p U hU y hy hfix hne

end Theory.AlgebraicGroup.ProperParabolicFixedRadical
