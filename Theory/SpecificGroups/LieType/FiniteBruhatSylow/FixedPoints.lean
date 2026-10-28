module

public import Theory.SpecificGroups.LieType.FiniteParabolicRealization
public import Theory.AlgebraicGroup.Tori.DefiningCharacteristic
public import Theory.GroupTheory.FiniteBruhatSylowCore
public import Theory.GroupTheory.FixedOrderedProduct

/-!
# Finite positive groups and ordered root-factor descent

The ambient finite group is the literal prime-to-p residual of Steinberg
fixed points. Its Borel, torus, normalizer and positive group candidates are
intersections with the corresponding algebraic point subgroups.

Unique ordered products of invariant unipotent blocks descend to this group:
uniqueness makes every coordinate fixed, and unipotence places each fixed
coordinate in the residual. The argument permits nonabelian blocks and uses
no crystallographic hypothesis on the relative Weyl group. To apply it to
GLS3 2.3.7, the blocks must be the full projected-ray preimages of 2.3.6,
including the nonreduced odd-unitary and Suzuki--Ree cases.

The invariant algebraic Borel decomposition gives a complement in the finite
Borel and hence a projection to its torus factor. `U N U` coverage and the
positive-root escape property imply positive normalizer containment. The
torus has no p-power torsion, so the p-group normalizer condition then proves
Sylow maximality. The actual root-ray blocks, Borel decomposition, escape
property and finite Bruhat construction remain geometric obligations. No
result here claims the complete Theorems 2.3.4--2.3.8 from the algebraic
sigma-setup alone.

Sources: GLS3, 2.3.4--2.3.8, and the ordered-product argument of 1.12.7.
-/

@[expose] public section

namespace Theory.AlgebraicGroup.FiniteBruhatSylow

open FiniteParabolicRealization

variable {k : Type*} [Field k] {K : Variety k} [AlgebraicGroup K]

abbrev borel (σ : AlgebraicEndomorphism K) (p : ℕ) (B : ClosedSubgroup K) :=
  restrict σ p B.toSubgroup

abbrev torus (σ : AlgebraicEndomorphism K) (p : ℕ) (T : ClosedSubgroup K) :=
  restrict σ p T.toSubgroup

abbrev positive (σ : AlgebraicEndomorphism K) (p : ℕ) (U : ClosedSubgroup K) :=
  restrict σ p U.toSubgroup

/-- Intersect with the algebraic torus normalizer. A finite torus can be too
small for its own finite normalizer to be the intended `N`. -/
abbrev normalizer (σ : AlgebraicEndomorphism K) (p : ℕ) (T : ClosedSubgroup K) :=
  restrict σ p (Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)))

section Positive

variable [IsAlgClosed k] (σ : AlgebraicEndomorphism K) (p : ℕ)
  [Fact p.Prime] [CharP k p]

include p in
private theorem torus_disjoint_unipotent (T U : ClosedSubgroup K)
    (hT : IsSubtorus T) (hU : IsUnipotentAlgebraicGroup U.carrierVariety) :
    Disjoint T.toSubgroup U.toSubgroup := by
  apply disjoint_iff_inf_le.mpr
  intro x hx
  obtain ⟨n, hn⟩ := U.isPGroup_of_unipotent hU p ⟨x, hx.2⟩
  exact hT.eq_one_of_mem_of_pow_prime_pow_eq_one hx.1 n
    (congrArg (fun z : U.toSubgroup => (z : Variety.Point K)) hn)

/-- The algebraic torus--unipotent factorization descends to the source
residual, not only to the full fixed group. The torus coordinate belongs to
the residual because the unipotent coordinate does. -/
theorem restricted_borel_isComplement
    (B U T : ClosedSubgroup K) (hUB : U.toSubgroup ≤ B.toSubgroup)
    (hTB : T.toSubgroup ≤ B.toSubgroup)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety) (hT : IsSubtorus T)
    (hσU : ∀ u ∈ U.toSubgroup, σ.onPoints u ∈ U.toSubgroup)
    (hσT : ∀ t ∈ T.toSubgroup, σ.onPoints t ∈ T.toSubgroup)
    (hdecomp : ∀ b ∈ B.toSubgroup, ∃ t ∈ T.toSubgroup, ∃ u ∈ U.toSubgroup,
      b = t * u) :
    ((torus σ p T).subgroupOf (borel σ p B)).IsComplement'
      ((positive σ p U).subgroupOf (borel σ p B)) := by
  have hd := torus_disjoint_unipotent p T U hT hU
  have hdfin : Disjoint ((torus σ p T).subgroupOf (borel σ p B))
      ((positive σ p U).subgroupOf (borel σ p B)) := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    apply Subtype.ext
    apply pointEmbedding_injective σ p
    exact disjoint_iff_inf_le.mp hd ⟨hx.1, hx.2⟩
  refine ⟨Subgroup.mul_injective_of_disjoint hdfin, ?_⟩
  intro x
  obtain ⟨t, ht, u, hu, hprod⟩ := hdecomp (pointEmbedding σ p x) x.property
  have hpair : ((⟨σ.onPoints t, hσT t ht⟩, ⟨σ.onPoints u, hσU u hu⟩) :
      T.toSubgroup × U.toSubgroup) = (⟨t, ht⟩, ⟨u, hu⟩) := by
    apply Subgroup.mul_injective_of_disjoint hd
    change σ.onPoints t * σ.onPoints u = t * u
    rw [← map_mul, ← hprod]
    exact x.val.val.property
  have hufix : σ.onPoints u = u :=
    congrArg (fun z : T.toSubgroup × U.toSubgroup => (z.2 : Variety.Point K)) hpair
  let u₀ : definingGroup σ p :=
    ⟨⟨u, hufix⟩, fixed_unipotent_le_definingGroup σ p U hU hu⟩
  let t₀ : definingGroup σ p := x.val * u₀⁻¹
  have ht₀ : pointEmbedding σ p t₀ = t := by
    change pointEmbedding σ p (x.val * u₀⁻¹) = t
    rw [map_mul, map_inv]
    change pointEmbedding σ p x.val * u⁻¹ = t
    rw [hprod, mul_inv_cancel_right]
  have huB : u₀ ∈ borel σ p B := hUB hu
  have htT : t₀ ∈ torus σ p T := by
    change pointEmbedding σ p t₀ ∈ T.toSubgroup
    rw [ht₀]
    exact ht
  have htB : t₀ ∈ borel σ p B := restrict_mono σ p hTB htT
  refine ⟨(⟨⟨t₀, htB⟩, htT⟩, ⟨⟨u₀, huB⟩, hu⟩), ?_⟩
  apply Subtype.ext
  exact inv_mul_cancel_right x.val u₀

/-- Once the positive normalizer is geometrically contained in the Borel,
the invariant algebraic Borel decomposition constructs its defining-
characteristic Sylow without an assumed finite projection or coprime index. -/
noncomputable def positiveSylowOfBorelDecomposition
    [Fact (IsAlgebraicSteinbergEndomorphism σ)]
    (B U T : ClosedSubgroup K) (hUB : U.toSubgroup ≤ B.toSubgroup)
    (hTB : T.toSubgroup ≤ B.toSubgroup)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety) (hT : IsSubtorus T)
    (hUN : (U.toSubgroup.subgroupOf B.toSubgroup).Normal)
    (hσU : ∀ u ∈ U.toSubgroup, σ.onPoints u ∈ U.toSubgroup)
    (hσT : ∀ t ∈ T.toSubgroup, σ.onPoints t ∈ T.toSubgroup)
    (hdecomp : ∀ b ∈ B.toSubgroup, ∃ t ∈ T.toSubgroup, ∃ u ∈ U.toSubgroup,
      b = t * u)
    (hnorm : Subgroup.normalizer (positive σ p U : Set (definingGroup σ p)) ≤
      borel σ p B) : Sylow p (definingGroup σ p) := by
  let : ((positive σ p U).subgroupOf (borel σ p B)).Normal :=
    restrict_normal σ p B.toSubgroup U.toSubgroup hUN
  refine Subgroup.sylowOfNormalizerComplement (positive σ p U) (borel σ p B)
    ((torus σ p T).subgroupOf (borel σ p B)) (restrict_isPGroup σ p U hU) hnorm
    (restricted_borel_isComplement σ p B U T hUB hTB hU hT hσU hσT hdecomp) ?_
  intro t n ht
  apply Subtype.ext
  apply Subtype.ext
  apply pointEmbedding_injective σ p
  apply hT.eq_one_of_mem_of_pow_prime_pow_eq_one t.property n
  simpa only [Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_subtype,
    map_pow, map_one] using congrArg
    (fun z : (torus σ p T).subgroupOf (borel σ p B) =>
      pointEmbedding σ p z.val.val) ht

@[simp] theorem coe_positiveSylowOfBorelDecomposition
    [Fact (IsAlgebraicSteinbergEndomorphism σ)]
    (B U T : ClosedSubgroup K) (hUB : U.toSubgroup ≤ B.toSubgroup)
    (hTB : T.toSubgroup ≤ B.toSubgroup)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety) (hT : IsSubtorus T)
    (hUN : (U.toSubgroup.subgroupOf B.toSubgroup).Normal)
    (hσU : ∀ u ∈ U.toSubgroup, σ.onPoints u ∈ U.toSubgroup)
    (hσT : ∀ t ∈ T.toSubgroup, σ.onPoints t ∈ T.toSubgroup)
    (hdecomp : ∀ b ∈ B.toSubgroup, ∃ t ∈ T.toSubgroup, ∃ u ∈ U.toSubgroup,
      b = t * u)
    (hnorm : Subgroup.normalizer (positive σ p U : Set (definingGroup σ p)) ≤
      borel σ p B) :
    (positiveSylowOfBorelDecomposition σ p B U T hUB hTB hU hT hUN hσU hσT
      hdecomp hnorm : Subgroup (definingGroup σ p)) = positive σ p U := rfl

/-- The finite Bruhat and root-transport producers feed the literal
finite-parabolic consumer. Normalizer containment, the torus projection and
Sylow maximality are all derived here. The remaining premises are algebraic
Borel decomposition, `U N U` coverage and a positive-root escape witness for
each non-Borel normalizer representative. -/
theorem finiteParabolic_contains_sylow_of_root_factorization
    [Fact (IsAlgebraicSteinbergEndomorphism σ)]
    (B U T : ClosedSubgroup K) (hUB : U.toSubgroup ≤ B.toSubgroup)
    (hTB : T.toSubgroup ≤ B.toSubgroup)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety) (hT : IsSubtorus T)
    (hUN : (U.toSubgroup.subgroupOf B.toSubgroup).Normal)
    (hσU : ∀ u ∈ U.toSubgroup, σ.onPoints u ∈ U.toSubgroup)
    (hσT : ∀ t ∈ T.toSubgroup, σ.onPoints t ∈ T.toSubgroup)
    (hdecomp : ∀ b ∈ B.toSubgroup, ∃ t ∈ T.toSubgroup, ∃ u ∈ U.toSubgroup,
      b = t * u)
    (hcover : ∀ g : definingGroup σ p, ∃ u ∈ positive σ p U,
      ∃ n ∈ normalizer σ p T, ∃ v ∈ positive σ p U, g = u * n * v)
    (hescape : ∀ n ∈ normalizer σ p T, n ∉ borel σ p B →
      ∃ u ∈ positive σ p U, n * u * n⁻¹ ∉ positive σ p U)
    {P : Subgroup (definingGroup σ p)} (hP : IsFiniteParabolic σ p B P) :
    ∃ S : Sylow p (definingGroup σ p), (S : Subgroup _) ≤ P := by
  have hnorm := Subgroup.normalizer_le_of_unipotent_factorization
    (positive σ p U) (borel σ p B) (normalizer σ p T)
    (restrict_mono σ p hUB) hcover hescape
  exact hP.contains_sylow σ p
    (positiveSylowOfBorelDecomposition σ p B U T hUB hTB hU hT hUN hσU hσT
      hdecomp hnorm) (restrict_mono σ p hUB)

/-- A geometric Borel projection and normalizer containment construct the
actual positive Sylow in the source residual. Existence of these two geometric
inputs is a separate obligation, not part of the definition of the setup. -/
noncomputable def positiveSylowOfNormalizerProjection
    [Fact (IsAlgebraicSteinbergEndomorphism σ)]
    (B U T : ClosedSubgroup K)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety) (hT : IsSubtorus T)
    (hnorm : Subgroup.normalizer (positive σ p U : Set (definingGroup σ p)) ≤
      borel σ p B)
    (π : borel σ p B →* Variety.Point T.carrierVariety)
    (hker : π.ker = (positive σ p U).subgroupOf (borel σ p B)) :
    Sylow p (definingGroup σ p) :=
  Subgroup.sylowOfNormalizerProjection (positive σ p U) (borel σ p B)
    (restrict_isPGroup σ p U hU) hnorm π hker
    (fun t n ht => hT.eq_one_of_pow_prime_pow_eq_one t n ht)

@[simp] theorem coe_positiveSylowOfNormalizerProjection
    [Fact (IsAlgebraicSteinbergEndomorphism σ)]
    (B U T : ClosedSubgroup K)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety) (hT : IsSubtorus T)
    (hnorm : Subgroup.normalizer (positive σ p U : Set (definingGroup σ p)) ≤
      borel σ p B)
    (π : borel σ p B →* Variety.Point T.carrierVariety)
    (hker : π.ker = (positive σ p U).subgroupOf (borel σ p B)) :
    (positiveSylowOfNormalizerProjection σ p B U T hU hT hnorm π hker :
      Subgroup (definingGroup σ p)) = positive σ p U := rfl

/-- Application to the literal finite-parabolic predicate used by the
realization consumer, with the positive Sylow premise now discharged. -/
theorem finiteParabolic_contains_sylow_of_normalizer_projection
    [Fact (IsAlgebraicSteinbergEndomorphism σ)]
    (B U T : ClosedSubgroup K) (hUB : U.toSubgroup ≤ B.toSubgroup)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety) (hT : IsSubtorus T)
    (hnorm : Subgroup.normalizer (positive σ p U : Set (definingGroup σ p)) ≤
      borel σ p B)
    (π : borel σ p B →* Variety.Point T.carrierVariety)
    (hker : π.ker = (positive σ p U).subgroupOf (borel σ p B))
    {P : Subgroup (definingGroup σ p)} (hP : IsFiniteParabolic σ p B P) :
    ∃ S : Sylow p (definingGroup σ p), (S : Subgroup _) ≤ P :=
  hP.contains_sylow σ p
    (positiveSylowOfNormalizerProjection σ p B U T hU hT hnorm π hker)
    (restrict_mono σ p hUB)

/-- Unique ordered algebraic block coordinates descend to the literal
residual group. Every factor lies in its specified restricted block. The
blocks need not be abelian and no individual absolute root need be invariant. -/
theorem existsUnique_restricted_ordered_factors
    {m : ℕ} (Y : Fin m → ClosedSubgroup K)
    (hY : ∀ i, IsUnipotentAlgebraicGroup (Y i).carrierVariety)
    (hσ : ∀ i x, x ∈ (Y i).toSubgroup → σ.onPoints x ∈ (Y i).toSubgroup)
    (hinj : Function.Injective (Subgroup.orderedProduct (fun i => (Y i).toSubgroup)))
    (x : definingGroup σ p)
    (hx : ∃ a : ∀ i, (Y i).toSubgroup,
      Subgroup.orderedProduct (fun i => (Y i).toSubgroup) a = pointEmbedding σ p x) :
    ∃! a : ∀ i, restrict σ p (Y i).toSubgroup,
      Subgroup.orderedProduct (fun i => restrict σ p (Y i).toSubgroup) a = x := by
  obtain ⟨a, ha⟩ := hx
  have hfixed : ∀ i, σ.onPoints (a i : Variety.Point K) = a i :=
    Subgroup.fixed_coordinates_of_orderedProduct_injective σ.onPoints
      (fun i => (Y i).toSubgroup) hσ hinj a (by
        rw [ha]
        exact x.val.property)
  let b : ∀ i, restrict σ p (Y i).toSubgroup := fun i =>
    ⟨⟨⟨a i, hfixed i⟩,
      fixed_unipotent_le_definingGroup σ p (Y i) (hY i) (a i).property⟩,
      (a i).property⟩
  have hb : Subgroup.orderedProduct (fun i => restrict σ p (Y i).toSubgroup) b = x := by
    apply pointEmbedding_injective σ p
    simpa only [Subgroup.orderedProduct, MonoidHom.map_list_prod, List.map_ofFn,
      b, pointEmbedding, MonoidHom.comp_apply, Subgroup.coe_subtype, Function.comp_def]
      using ha
  refine ⟨b, hb, ?_⟩
  intro c hc
  let d : ∀ i, (Y i).toSubgroup := fun i =>
    ⟨pointEmbedding σ p (c i), (c i).property⟩
  have hd : Subgroup.orderedProduct (fun i => (Y i).toSubgroup) d =
      pointEmbedding σ p x := by
    simpa only [Subgroup.orderedProduct, MonoidHom.map_list_prod, List.map_ofFn,
      d, Function.comp_def]
      using congrArg (pointEmbedding σ p) hc
  have heq := hinj (hd.trans ha.symm)
  funext i
  apply Subtype.ext
  apply pointEmbedding_injective σ p
  exact congrArg (fun z : ∀ i, (Y i).toSubgroup => (z i : Variety.Point K)) heq

end Positive

end Theory.AlgebraicGroup.FiniteBruhatSylow

end
