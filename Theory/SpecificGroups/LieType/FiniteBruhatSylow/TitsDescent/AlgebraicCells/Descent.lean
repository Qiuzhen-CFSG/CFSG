module

public import Theory.SpecificGroups.LieType.FiniteBruhatSylow.TitsDescent.AlgebraicCells
public import Theory.SpecificGroups.LieType.FiniteBruhatSylow.TitsDescent

/-!
# Application of algebraic root cells to the defining residual

Apply the constructed opposite-Borel cell geometry to the literal
`existsUnique_defining_normalForm` consumer. Invariance, generation and
simple-lift exchange remain the independent inputs of the finite-descent
owner. The root-geometry premises are exactly those still explicit in the
algebraic construction; this application does not discharge them.

Source: GLS3 1.11.5 and 2.3.5.
-/

public section
namespace Theory.AlgebraicGroup.FiniteBruhatSylow.TitsDescent.AlgebraicCells

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {K : Variety k} [AlgebraicGroup K]

/-- Actual-root collection and algebraic separation supply the complete
geometry premise of finite defining-residual descent. -/
theorem existsUnique_defining_normalForm_of_realized_roots
    (σ : AlgebraicEndomorphism K) (p : ℕ) [Fact p.Prime] [CharP k p]
    (B C U V T : ClosedSubgroup K)
    (hB : IsBorelSubgroup B) (hC : IsBorelSubgroup C)
    (hU : IsUnipotentRadicalOf B U) (hV : IsUnipotentRadicalOf C V)
    (hT : IsMaximalTorus T) (hBC : B.inter C = T)
    (hfixed : (U.pointwiseCentralizer T).toSubgroup = ⊥)
    (D : RootGroupData K T) (hD : D.IsRealization)
    (hmult : ∀ a, RootWeightSpaceMultiplicityOne T (D.rootWeight a))
    (hP : IsPositiveSystem D (D.borelRootSupport B))
    (hQ : IsPositiveSystem D (D.borelRootSupport C))
    (hgenerate : U.toSubgroup ≤ RootSubgroupGenerated D (D.borelRootSupport B))
    (hproduct : ∀ order : List D.Root, order.Nodup →
      (∀ a, a ∈ order ↔ a ∈ D.borelRootSupport B) →
      ∀ q ∈ RootSubgroupGenerated D (D.borelRootSupport B),
        ∃ xs : List (Variety.Point K),
          List.Forall₂ (fun a x => x ∈ D.rootSubgroup a) order xs ∧ xs.prod = q)
    (hσU : ∀ x ∈ U.toSubgroup, σ.onPoints x ∈ U.toSubgroup)
    (hσN : ∀ x ∈ T.normalizer.toSubgroup, σ.onPoints x ∈ T.normalizer.toSubgroup)
    (hσV : ∀ x ∈ V.toSubgroup, σ.onPoints x ∈ V.toSubgroup)
    (S : Set (Variety.Point K))
    (hBN : Subgroup.closure ((B.toSubgroup : Set (Variety.Point K)) ∪
      (T.normalizer.toSubgroup : Set (Variety.Point K))) = ⊤)
    (hN : T.normalizer.toSubgroup ≤ Subgroup.closure ((B.toSubgroup : Set _) ∪ S))
    (hSN : S ⊆ (T.normalizer.toSubgroup : Set (Variety.Point K)))
    (hsquare : ∀ s ∈ S, s * s ∈ B.toSubgroup)
    (hexchange : BruhatGeneration.SimpleLiftExchange B.toSubgroup T.normalizer.toSubgroup S)
    (g : FiniteParabolicRealization.definingGroup σ p) :
    ∃! a : NormalForm (positive σ p U)
      (normalizer σ p T)
      (FiniteParabolicRealization.restrict σ p V.toSubgroup), normalProduct a = g := by
  obtain ⟨R⟩ := nonempty_rootCellGeometry_of_realized_roots hB hC hU hV hT hBC
    hfixed D hD hmult hP hQ hgenerate hproduct
  exact existsUnique_defining_normalForm σ p B U T V hU.2.1 R hσU hσN hσV S
    hBN hN hSN hsquare hexchange g

end Theory.AlgebraicGroup.FiniteBruhatSylow.TitsDescent.AlgebraicCells
end
