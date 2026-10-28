module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.Coordinates
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.FixedQuotient
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.Commutators

/-!
# The symplectic point-local extension

The determinant-one point stabilizer maps onto the actual SL₂ through its
action on the perpendicular space modulo the fixed point. Its normal radical
has elementary abelian coordinates (u,v,z), and its central fixed subgroup
consists exactly of the elements (0,0,z). The central quotient is the additive
natural two-space, with conjugation by every local element given by its literal
SL₂ quotient matrix. Over a finite field of characteristic two and order greater
than two, commutators with upper and lower Levi transvections generate the radical.

`pointLocal_extension_spec` assembles these assertions for the explicit maps
on the original determinant kernel. The proofs use the fixed column and row,
the radical multiplication law, and the first isomorphism theorem. The adapter
in `Point.NaturalExtension` supplies the shared recognition interface. Two-core,
perfectness, block, and residual recognition belong to the consuming modules.

Source: Aschbacher--Smith, F.1.12(I)(2), printed pp.262--264.
-/

public section
open Matrix
namespace Theory.SpecificGroups.SymplecticFour

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The explicit point-local extension and its natural central quotient,
without any recognition or perfectness assumption. -/
theorem pointLocal_extension_spec {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n) :
    (pointRadical (F := F)).Normal ∧
    Function.Surjective (pointQuotient (F := F)) ∧
    (pointQuotient (F := F)).ker = pointRadical ∧
    IsElementaryAbelian 2 (pointRadical (F := F)) ∧
    Monoid.exponent (pointRadical (F := F)) = 2 ∧
    ⁅pointRadical (F := F), (⊤ : Subgroup (pointLocal (F := F)))⁆ = pointRadical ∧
    (Subgroup.center (pointLocal (F := F))).subgroupOf pointRadical =
      pointRadicalVector.ker ∧
    (∀ q : pointRadical (F := F),
      q ∈ (Subgroup.center (pointLocal (F := F))).subgroupOf pointRadical ↔
        ∃ z : F, q.val = pointRadicalElement 0 0 z) ∧
    (∀ (l : pointLocal (F := F)) (q : pointRadical (F := F)),
      pointCentralQuotientEquiv (QuotientGroup.mk (pointRadicalConjugate l q)) =
        Multiplicative.ofAdd ((pointQuotient l).val *ᵥ
          (pointCentralQuotientEquiv (QuotientGroup.mk q)).toAdd)) := by
  exact ⟨inferInstance, pointQuotient_surjective, pointQuotient_ker, inferInstance,
    pointRadical_exponent, pointRadical_commutator_eq hcard hn,
    pointRadical_center_eq_vector_ker, pointRadical_mem_center_iff,
    pointCentralQuotientEquiv_conjugate⟩

end Theory.SpecificGroups.SymplecticFour
