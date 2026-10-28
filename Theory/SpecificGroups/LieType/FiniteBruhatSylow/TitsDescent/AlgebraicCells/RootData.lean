module

public import Theory.SpecificGroups.LieType.FiniteBruhatSylow.TitsDescent.AlgebraicCells.Basic
public import Theory.AlgebraicGroup.Borel.RootSupport
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.InvariantRootList
public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.NormalizerActionExistence.Action

/-!
# Actual root data in the opposite-Borel cell construction

The root supports of opposite Borels are disjoint, because a common root
group would lie in their torus intersection. If both supports are positive
systems, they therefore cover every root. Same-weight root-subgroup
uniqueness transports every actual root under each actual torus normalizer
element, so its image lies in one of the two actual radicals.

This discharges the sign-transport and enumeration premises of the ordered
collection construction. The remaining premises are actual root realization,
Borel support positivity and generation, multiplicity one,
trivial radical fixed points, and the arbitrary-order product theorem. Their
construction from reductivity remains with the source assembly.

Source: GLS3 1.9.5, 1.11.2--1.11.5, and 1.12.7(a),
`refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
namespace Theory.AlgebraicGroup.FiniteBruhatSylow.TitsDescent.AlgebraicCells

open BorelIntersectionGeometry.RankOneGeometry.NormalizerActionExistence

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {K : Variety k} [AlgebraicGroup K]
  {B C U V T : ClosedSubgroup K} {D : RootGroupData K T}

/-- Positive root supports of opposite Borels cover all actual roots. -/
theorem root_le_borel_or_opposite (hD : D.IsRealization)
    (hT : IsSubtorus T) (hBC : B.inter C = T)
    (hP : IsPositiveSystem D (D.borelRootSupport B))
    (hQ : IsPositiveSystem D (D.borelRootSupport C)) (a : D.Root) :
    D.rootSubgroup a ≤ B ∨ D.rootSubgroup a ≤ C := by
  have hdisjoint (b : D.Root) (hbB : D.rootSubgroup b ≤ B)
      (hbC : D.rootSubgroup b ≤ C) : False := by
    have hroot := (hD.2.2.1 b).1
    apply hroot.invariant_unipotent_ne_bot.2.2
    apply le_antisymm _ bot_le
    intro x hx
    have hxT : x ∈ T.toSubgroup := by
      change x ∈ T
      rw [← hBC]
      exact ⟨hbB hx, hbC hx⟩
    have hh : x ∈ (D.rootSubgroup b).toSubgroup ⊓ T.toSubgroup := ⟨hx, hxT⟩
    rwa [hroot.inf_torus_eq_bot hT] at hh
  by_cases ha : D.rootSubgroup a ≤ B
  · exact Or.inl ha
  have hp : a ∈ D.borelRootSupport B ∪ D.neg ⁻¹' D.borelRootSupport B := by
    rw [hP.2.1]
    trivial
  have hneg : D.rootSubgroup (D.neg a) ≤ B := hp.resolve_left ha
  have hq : a ∈ D.borelRootSupport C ∪ D.neg ⁻¹' D.borelRootSupport C := by
    rw [hQ.2.1]
    trivial
  rcases hq with h | h
  · exact Or.inr h
  · exact (hdisjoint (D.neg a) hneg h).elim

/-- Actual normalizer conjugation sends each root group into one of the
two actual radicals. This uses neither a Weyl model nor cell absorption. -/
theorem root_subgroup_transport_sign (hD : D.IsRealization)
    (hmult : ∀ a, RootWeightSpaceMultiplicityOne T (D.rootWeight a))
    (hB : IsBorelSubgroup B) (hC : IsBorelSubgroup C)
    (hU : IsUnipotentRadicalOf B U) (hV : IsUnipotentRadicalOf C V)
    (hT : IsSubtorus T) (hBC : B.inter C = T)
    (hP : IsPositiveSystem D (D.borelRootSupport B))
    (hQ : IsPositiveSystem D (D.borelRootSupport C))
    (n : T.normalizer.toSubgroup) (a : D.Root) :
    (D.rootSubgroup a).toSubgroup ≤ U.toSubgroup.comap (MulAut.conj n.val).toMonoidHom ∨
    (D.rootSubgroup a).toSubgroup ≤ V.toSubgroup.comap (MulAut.conj n.val).toMonoidHom := by
  have hmaps : (D.rootSubgroup a).toSubgroup ≤
      (D.rootSubgroup (rootAction hD n a)).toSubgroup.comap
        (MulAut.conj n.val).toMonoidHom := by
    intro x hx
    change n.val * x * n.val⁻¹ ∈ D.rootSubgroup (rootAction hD n a)
    rw [← rootAction_transport hD hmult n a, ClosedSubgroup.mem_conjugate_iff]
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
      inv_mul_cancel, mul_one] using hx
  have hu := (hD.2.2.1 (rootAction hD n a)).1.2.isUnipotentAlgebraicGroup
  rcases root_le_borel_or_opposite hD hT hBC hP hQ (rootAction hD n a) with h | h
  · left
    intro x hx
    exact hU.contains_unipotent_closedSubgroup hB.connected hB.solvable h hu (hmaps hx)
  · right
    intro x hx
    exact hV.contains_unipotent_closedSubgroup hC.connected hC.solvable h hu (hmaps hx)

/-- Specialize the collection construction to the actual roots at `T`.
Only the arbitrary-order product premise remains from root collection. -/
theorem nonempty_rootCellGeometry_of_realized_roots
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
          List.Forall₂ (fun a x => x ∈ D.rootSubgroup a) order xs ∧ xs.prod = q) :
    Nonempty (RootCellGeometry B.toSubgroup U.toSubgroup T.toSubgroup
      T.normalizer.toSubgroup V.toSubgroup) := by
  obtain ⟨roots, hnd, hroots⟩ := finite_contained_root_list T B D hD
  apply nonempty_rootCellGeometry_of_ordered_products hB hU hV hT hBC hfixed
    (fun a => (D.rootSubgroup a).toSubgroup) (D.borelRootSupport B) roots hnd hroots
  · intro a ha
    exact hU.contains_unipotent_closedSubgroup hB.connected hB.solvable ha
      (hD.2.2.1 a).1.2.isUnipotentAlgebraicGroup
  · intro order horder hmem q hq
    exact hproduct order horder hmem q (hgenerate hq)
  · intro n hn a _
    exact root_subgroup_transport_sign hD hmult hB hC hU hV hT.1 hBC hP hQ ⟨n, hn⟩ a

end Theory.AlgebraicGroup.FiniteBruhatSylow.TitsDescent.AlgebraicCells
end
