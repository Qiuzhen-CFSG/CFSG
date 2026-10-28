module

public import Theory.SpecificGroups.LieType.FiniteBruhatSylow.FixedPoints
public import Theory.SpecificGroups.LieType.FiniteBruhatSylow.TitsDescent.RootCells

/-!
# Descent of root Bruhat normal forms to the defining residual

Local root-cell separation and collection, together with ambient generation
and simple-lift exchange, give a unique ambient `u*n*v` expression. Applying
sigma and using uniqueness fixes every factor. Fixed unipotent elements lie
in the prime-to-p residual, so the middle factor also lies there by
`n = u⁻¹*g*v⁻¹`. The same argument applies to every intermediate subgroup
between that residual and the full fixed group.

The root-cell geometry and ambient generation/exchange premises are explicit
construction obligations. This module does not yet construct a finite Tits
system, identify its Weyl quotient, or assert the source theorem from a sigma
setup alone. No global coverage or BN-pair certificate is an input.

Source: GLS3 2.3.4--2.3.5 and the algebraic normal form 1.11.5;
`refs/KGroup/GLS3/chapter2.tex` and `refs/KGroup/GLS3/Chapter1.tex`.
-/

@[expose] public section
namespace Theory.AlgebraicGroup.FiniteBruhatSylow.TitsDescent
open FiniteParabolicRealization

variable {k : Type*} [Field k] {K : Variety k} [AlgebraicGroup K]

/-- The literal inclusion of an intermediate fixed subgroup into algebraic points. -/
def intermediateEmbedding (σ : AlgebraicEndomorphism K)
    (L : Subgroup (fixedPoints σ)) : L →* Variety.Point K :=
  (fixedPoints σ).subtype.comp L.subtype

/-- The local algebraic cell geometry identifies the literal finite intersection. -/
theorem restricted_borel_inf_normalizer (σ : AlgebraicEndomorphism K) (p : ℕ)
    (B U T V : ClosedSubgroup K)
    (R : RootCellGeometry B.toSubgroup U.toSubgroup T.toSubgroup
      (Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K))) V.toSubgroup) :
    borel σ p B ⊓ normalizer σ p T = torus σ p T := by
  ext x
  change pointEmbedding σ p x ∈ B.toSubgroup ⊓
    Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)) ↔
      pointEmbedding σ p x ∈ T.toSubgroup
  rw [R.borel_inf_normalizer]

/-- The finite inversion subgroup uses the source's right conjugation and
literal point embedding. A long-element lift identifying the opposite is a
separate geometric input. -/
theorem restricted_rightFactor_eq_source (σ : AlgebraicEndomorphism K) (p : ℕ)
    (U V : ClosedSubgroup K) (n₀ n : definingGroup σ p)
    (hV : V.toSubgroup = U.toSubgroup.comap
      (MulAut.conj (pointEmbedding σ p n₀)).toMonoidHom) :
    rightFactor (positive σ p U) (restrict σ p V.toSubgroup) n =
      positive σ p U ⊓ (positive σ p U).comap
        (MulAut.conj (n₀ * n)).toMonoidHom := by
  have hVfin : restrict σ p V.toSubgroup =
      (positive σ p U).comap (MulAut.conj n₀).toMonoidHom := by
    ext x
    change pointEmbedding σ p x ∈ V.toSubgroup ↔
      pointEmbedding σ p (n₀ * x * n₀⁻¹) ∈ U.toSubgroup
    rw [hV]
    change pointEmbedding σ p n₀ * pointEmbedding σ p x *
      (pointEmbedding σ p n₀)⁻¹ ∈ U.toSubgroup ↔ _
    rw [map_mul, map_mul, map_inv]
  rw [hVfin, rightFactor_rightConjugate]

section Descent
variable [IsAlgClosed k] (σ : AlgebraicEndomorphism K) (p : ℕ)
  [Fact p.Prime] [CharP k p]
  (B U T V : ClosedSubgroup K)
  (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
  (R : RootCellGeometry B.toSubgroup U.toSubgroup T.toSubgroup
    (Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K))) V.toSubgroup)
  (hσU : ∀ x ∈ U.toSubgroup, σ.onPoints x ∈ U.toSubgroup)
  (hσN : ∀ x ∈ Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)),
    σ.onPoints x ∈ Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)))
  (hσV : ∀ x ∈ V.toSubgroup, σ.onPoints x ∈ V.toSubgroup)
  (S : Set (Variety.Point K))
  (hBN : Subgroup.closure ((B.toSubgroup : Set (Variety.Point K)) ∪
    (Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)) :
      Set (Variety.Point K))) = ⊤)
  (hN : Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)) ≤
    Subgroup.closure ((B.toSubgroup : Set (Variety.Point K)) ∪ S))
  (hSN : S ⊆ Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)))
  (hsquare : ∀ s ∈ S, s * s ∈ B.toSubgroup)
  (hexchange : BruhatGeneration.SimpleLiftExchange B.toSubgroup
    (Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K))) S)

include hU R hσU hσN hσV hBN hN hSN hsquare hexchange

/-- Unique normal forms descend to every literal intermediate fixed group.
Both outer factors belong to the defining residual; this forces the middle
factor to belong to the specified intermediate group. -/
theorem existsUnique_intermediate_normalForm
    (L : Subgroup (fixedPoints σ)) (hKL : definingGroup σ p ≤ L) (g : L) :
    ∃! a : NormalForm
      (U.toSubgroup.comap (intermediateEmbedding σ L))
      ((Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K))).comap
        (intermediateEmbedding σ L))
      (V.toSubgroup.comap (intermediateEmbedding σ L)), normalProduct a = g := by
  let f := intermediateEmbedding σ L
  have hf : Function.Injective f := Subtype.coe_injective.comp Subtype.coe_injective
  obtain ⟨a, ha, _⟩ := R.existsUnique_normalForm_of_simpleLiftExchange
    S hBN hN hSN hsquare hexchange (f g)
  have hfixed := R.fixed_coordinates σ.onPoints hσU hσN hσV a (by
    rw [ha]
    exact g.val.property)
  let u : L := ⟨⟨a.val.1, hfixed.1⟩,
    hKL (fixed_unipotent_le_definingGroup σ p U hU a.property.1)⟩
  let v : L := ⟨⟨a.val.2.2, hfixed.2.2⟩,
    hKL (fixed_unipotent_le_definingGroup σ p U hU a.property.2.2.1)⟩
  let n : L := u⁻¹ * g * v⁻¹
  have hn : f n = a.val.2.1 := by
    change f (u⁻¹ * g * v⁻¹) = a.val.2.1
    rw [map_mul, map_mul, map_inv, map_inv]
    change a.val.1⁻¹ * f g * a.val.2.2⁻¹ = a.val.2.1
    rw [← ha]
    dsimp [normalProduct]
    group
  let a₀ : NormalForm (U.toSubgroup.comap f)
      ((Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K))).comap f)
      (V.toSubgroup.comap f) :=
    ⟨(u, n, v), a.property.1, by
      change f n ∈ Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K))
      rw [hn]
      exact a.property.2.1,
      a.property.2.2.1, by
        change f (n * v * n⁻¹) ∈ V.toSubgroup
        rw [map_mul, map_mul, map_inv, hn]
        exact a.property.2.2.2⟩
  have ha₀ : normalProduct a₀ = g := by
    change u * (u⁻¹ * g * v⁻¹) * v = g
    group
  refine ⟨a₀, ha₀, ?_⟩
  intro b hb
  apply NormalForm.map_injective (U' := U.toSubgroup)
    (N' := Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)))
    (V' := V.toSubgroup) f hf
    (fun _ hx => hx) (fun _ hx => hx) (fun _ hx => hx)
  apply R.normalProduct_injective
  simpa only [normalProduct, NormalForm.map, map_mul] using
    congrArg f (hb.trans ha₀.symm)

/-- Unique normal forms in the source residual, with the published positive
and normalizer subgroups and with the complete torus parameter in `n`. -/
theorem existsUnique_defining_normalForm (g : definingGroup σ p) :
    ∃! a : NormalForm (positive σ p U) (normalizer σ p T)
      (restrict σ p V.toSubgroup), normalProduct a = g :=
  existsUnique_intermediate_normalForm σ p B U T V hU R hσU hσN hσV S
    hBN hN hSN hsquare hexchange (definingGroup σ p) le_rfl g

/-- The exact coverage premise of
`finiteParabolic_contains_sylow_of_root_factorization`, derived from local
root geometry and ambient generation/exchange. -/
theorem definingGroup_unu_coverage (g : definingGroup σ p) :
    ∃ u ∈ positive σ p U, ∃ n ∈ normalizer σ p T,
      ∃ v ∈ positive σ p U, g = u * n * v := by
  obtain ⟨a, ha, _⟩ := existsUnique_defining_normalForm σ p B U T V hU R
    hσU hσN hσV S hBN hN hSN hsquare hexchange g
  exact ⟨a.val.1, a.property.1, a.val.2.1, a.property.2.1,
    a.val.2.2, a.property.2.2.1, ha.symm⟩
/-- Application to the published finite-parabolic consumer. The remaining
root escape and Borel geometry premises are owned by the root-ray producer;
the global finite coverage premise has been discharged here. -/
theorem finiteParabolic_contains_sylow_of_local_root_cells
    [Fact (IsAlgebraicSteinbergEndomorphism σ)]
    (hT : IsSubtorus T)
    (hUN : (U.toSubgroup.subgroupOf B.toSubgroup).Normal)
    (hσT : ∀ x ∈ T.toSubgroup, σ.onPoints x ∈ T.toSubgroup)
    (hescape : ∀ n ∈ normalizer σ p T, n ∉ borel σ p B →
      ∃ u ∈ positive σ p U, n * u * n⁻¹ ∉ positive σ p U)
    {P : Subgroup (definingGroup σ p)} (hP : IsFiniteParabolic σ p B P) :
    ∃ Q : Sylow p (definingGroup σ p), (Q : Subgroup _) ≤ P := by
  exact finiteParabolic_contains_sylow_of_root_factorization σ p B U T
    R.positive_le R.torus_le_borel hU hT hUN hσU hσT R.torus_positive_factors
    (definingGroup_unu_coverage σ p B U T V hU R hσU hσN hσV S
      hBN hN hSN hsquare hexchange) hescape hP


end Descent
end Theory.AlgebraicGroup.FiniteBruhatSylow.TitsDescent
end
