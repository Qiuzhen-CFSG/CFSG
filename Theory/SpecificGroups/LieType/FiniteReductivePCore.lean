module

public import Theory.SpecificGroups.LieType.InvariantParabolicLevi
public import Theory.GroupTheory.PResidual.PrimeToCoreRestriction
public import Theory.GroupTheory.PResidual.PrimeToMonotone

/-!
# P-cores of finite Levi intersections

The source Levi is `L ∩ O^{p′}(K^sigma)`, whereas its full fixed group is
`L ∩ K^sigma`. We construct the inclusion between these literal groups and
prove that it preserves the p-core. Its image contains the intrinsic
prime-to-p residual of the full fixed Levi; it need not equal that residual.
In particular the source Levi is p-reduced exactly when the full fixed Levi is.

A positive Sylow in the intrinsic residual and a fixed opposition element
with disjoint unipotent factors then imply p-reducedness and discharge the
`hLcore` argument of `InvariantParabolicLevi.radical_eq_pCore_of_decomposition`.
The Sylow and opposition hypotheses are explicit earlier-source inputs, not
consequences proved here from reductivity alone. Their producer is the finite
Bruhat/root geometry of GLS3 §2.3, also for the reductive Levi. No simplicity,
perfectness, untwistedness or field-size restriction is imposed.

The closed-Levi endomorphism and its fixed-point comparison are constructed in
`FiniteReductivePCore.ClosedLevi`.

Sources: GLS3, 2.2.7, 2.6.2 and the proof of 2.6.5(e,f). The transcription
sentence `U_J = O_r(L_J)` at the end of that proof must be read with `P_J`:
part (e) itself states `U_J = O_r(P_J)`.
-/

@[expose] public section

namespace Theory.AlgebraicGroup.FiniteReductivePCore
open FiniteParabolicRealization
variable {k : Type*} [Field k] {K : Variety k} [AlgebraicGroup K]

/-- Full fixed points of an ambient point subgroup. -/
abbrev fullFixed (σ : AlgebraicEndomorphism K) (H : Subgroup (Variety.Point K)) :=
  H.comap (fixedPoints σ).subtype

/-- Include the full fixed subgroup in the algebraic point group. -/
def fullFixedPointEmbedding (σ : AlgebraicEndomorphism K) (H : Subgroup (Variety.Point K)) :
    fullFixed σ H →* Variety.Point K :=
  (fixedPoints σ).subtype.comp (fullFixed σ H).subtype

theorem fullFixedPointEmbedding_injective (σ : AlgebraicEndomorphism K)
    (H : Subgroup (Variety.Point K)) : Function.Injective (fullFixedPointEmbedding σ H) :=
  Subtype.coe_injective.comp Subtype.coe_injective

/-- The actual finite intersection, viewed inside the full fixed subgroup. -/
abbrev intermediate (σ : AlgebraicEndomorphism K) (p : ℕ)
    (H : Subgroup (Variety.Point K)) : Subgroup (fullFixed σ H) :=
  (definingGroup σ p).comap (fullFixed σ H).subtype

/-- Reassociate the two subgroup conditions without changing the point. -/
def restrictedEquivIntermediate (σ : AlgebraicEndomorphism K) (p : ℕ)
    (H : Subgroup (Variety.Point K)) : restrict σ p H ≃* intermediate σ p H where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The literal inclusion of the finite Levi into its full fixed group. -/
def restrictedEmbedding (σ : AlgebraicEndomorphism K) (p : ℕ)
    (H : Subgroup (Variety.Point K)) : restrict σ p H →* fullFixed σ H :=
  (intermediate σ p H).subtype.comp (restrictedEquivIntermediate σ p H).toMonoidHom

theorem restrictedEmbedding_injective (σ : AlgebraicEndomorphism K) (p : ℕ)
    (H : Subgroup (Variety.Point K)) : Function.Injective (restrictedEmbedding σ p H) :=
  Subtype.coe_injective.comp (restrictedEquivIntermediate σ p H).injective

theorem restrictedEmbedding_range (σ : AlgebraicEndomorphism K) (p : ℕ)
    (H : Subgroup (Variety.Point K)) :
    (restrictedEmbedding σ p H).range = intermediate σ p H := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (restrictedEquivIntermediate σ p H y).property
  · intro hx
    exact ⟨(restrictedEquivIntermediate σ p H).symm ⟨x, hx⟩, rfl⟩

/-- The actual intersection contains, but need not equal, the intrinsic residual. -/
theorem primeToResidual_le_intermediate (σ : AlgebraicEndomorphism K) (p : ℕ)
    (H : Subgroup (Variety.Point K)) :
    Subgroup.primeToResidual p (fullFixed σ H) ≤ intermediate σ p H :=
  Subgroup.map_le_iff_le_comap.mp
    (Subgroup.map_primeToResidual_le_of_hom p (fullFixed σ H).subtype)

/-- Normality holds in the full fixed Levi, without ambient normality of the Levi. -/
theorem intermediate_normal (σ : AlgebraicEndomorphism K) (p : ℕ)
    (H : Subgroup (Variety.Point K)) : (intermediate σ p H).Normal := inferInstance

/-- The inclusion preserves the embedded p-core. -/
theorem map_pCore_restrictedEmbedding (σ : AlgebraicEndomorphism K) (p : ℕ)
    (H : Subgroup (Variety.Point K)) :
    (pCore p (restrict σ p H)).map (restrictedEmbedding σ p H) =
      pCore p (fullFixed σ H) := by
  change (pCore p (restrict σ p H)).map
    ((intermediate σ p H).subtype.comp (restrictedEquivIntermediate σ p H).toMonoidHom) = _
  rw [← Subgroup.map_map, pCore_map_iso]
  exact Subgroup.map_pCore_eq_of_primeToResidual_le p _
    (primeToResidual_le_intermediate σ p H)

/-- P-reducedness is equivalent for the two different finite Levi groups. -/
theorem restrict_pCore_eq_bot_iff (σ : AlgebraicEndomorphism K) (p : ℕ)
    (H : Subgroup (Variety.Point K)) :
    pCore p (restrict σ p H) = ⊥ ↔ pCore p (fullFixed σ H) = ⊥ := by
  constructor
  · intro h
    rw [← map_pCore_restrictedEmbedding σ p H, h, Subgroup.map_bot]
  · intro h
    apply Subgroup.map_injective (restrictedEmbedding_injective σ p H)
    rw [map_pCore_restrictedEmbedding, h, Subgroup.map_bot]

/-- Positive Sylow and opposition geometry kill the full fixed p-core. -/
theorem fullFixed_pCore_eq_bot_of_residualSylow_opposition
    (σ : AlgebraicEndomorphism K) (p : ℕ) (H U : Subgroup (Variety.Point K))
    (S : Sylow p (Subgroup.primeToResidual p (fullFixed σ H)))
    (hS : (S : Subgroup _).map ((fullFixedPointEmbedding σ H).comp
      (Subgroup.primeToResidual p (fullFixed σ H)).subtype) ≤ U)
    (n : fullFixed σ H)
    (hdis : Disjoint U (U.map (MulAut.conj (fullFixedPointEmbedding σ H n)).toMonoidHom)) :
    pCore p (fullFixed σ H) = ⊥ :=
  Subgroup.pCore_eq_bot_of_residualSylow_opposition p _
    (fullFixedPointEmbedding_injective σ H) U S hS n hdis

/-- The same geometry kills the p-core of the source intersection. -/
theorem restrict_pCore_eq_bot_of_residualSylow_opposition
    (σ : AlgebraicEndomorphism K) (p : ℕ) (H U : Subgroup (Variety.Point K))
    (S : Sylow p (Subgroup.primeToResidual p (fullFixed σ H)))
    (hS : (S : Subgroup _).map ((fullFixedPointEmbedding σ H).comp
      (Subgroup.primeToResidual p (fullFixed σ H)).subtype) ≤ U)
    (n : fullFixed σ H)
    (hdis : Disjoint U (U.map (MulAut.conj (fullFixedPointEmbedding σ H n)).toMonoidHom)) :
    pCore p (restrict σ p H) = ⊥ :=
  (restrict_pCore_eq_bot_iff σ p H).mpr
    (fullFixed_pCore_eq_bot_of_residualSylow_opposition σ p H U S hS n hdis)

section Application
variable [IsAlgClosed k] (σ : AlgebraicEndomorphism K) (p : ℕ)
    [Fact p.Prime] [CharP k p] [Fact (IsAlgebraicSteinbergEndomorphism σ)]

/-- Supply the p-reduced Levi premise to the actual finite radical consumer. -/
theorem radical_eq_pCore_of_decomposition_of_residualSylow_opposition
    (P U L : ClosedSubgroup K)
    (hUP : U.toSubgroup ≤ P.toSubgroup) (hLP : L.toSubgroup ≤ P.toSubgroup)
    (hN : (U.toSubgroup.subgroupOf P.toSubgroup).Normal)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (hdis : Disjoint U.toSubgroup L.toSubgroup)
    (hσU : ∀ u ∈ U, σ.onPoints u ∈ U)
    (hσL : ∀ l ∈ L, σ.onPoints l ∈ L)
    (hmul : ∀ x ∈ P, ∃ u ∈ U, ∃ l ∈ L, x = u * l)
    (V : Subgroup (Variety.Point K))
    (S : Sylow p (Subgroup.primeToResidual p (fullFixed σ L.toSubgroup)))
    (hS : (S : Subgroup _).map ((fullFixedPointEmbedding σ L.toSubgroup).comp
      (Subgroup.primeToResidual p (fullFixed σ L.toSubgroup)).subtype) ≤ V)
    (n : fullFixed σ L.toSubgroup)
    (hopp : Disjoint V
      (V.map (MulAut.conj (fullFixedPointEmbedding σ L.toSubgroup n)).toMonoidHom)) :
    restrict σ p U.toSubgroup =
      (pCore p (restrict σ p P.toSubgroup)).map (restrict σ p P.toSubgroup).subtype :=
  InvariantParabolicLevi.radical_eq_pCore_of_decomposition σ p P U L
    hUP hLP hN hU hdis hσU hσL hmul
    (restrict_pCore_eq_bot_of_residualSylow_opposition σ p L.toSubgroup V S hS n hopp)
end Application

end Theory.AlgebraicGroup.FiniteReductivePCore
