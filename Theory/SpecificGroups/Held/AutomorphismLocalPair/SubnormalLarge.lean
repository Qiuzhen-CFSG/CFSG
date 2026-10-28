module
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SeedIdentification
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge.ResidualNine
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge.CubicCommutators
public import Theory.GroupTheory.PResidual.SubnormalNineQuotient

/-!
# Subnormal order restrictions in the invariant Held seed normalizer

Two finite calculations on the literal representative suffice: the two-residual
has two-core quotient of order nine, and every cubic element has a seed
commutator subgroup of order greater than twelve. The general relative
subnormal argument then gives the required order alternatives. Sylow
conjugacy transports the result to every canonical large local, through an
explicit equivalence whose underlying function is Held conjugation.

The certified residual quotient supplies the sole premise of the cubic
commutator calculation. Combining them proves the unconditional native
order restriction, retaining the conditional transport APIs as well. The
seed is the join of both normal elementary order-64 subgroups. This is the
finite-model input to the Held block exclusion; the ambient source assembly
belongs to its classification consumer.

Source: Aschbacher--Smith 2.3.9(7), printed p.526; GLS3 Table 5.3p and its
convention for the two local classes fused by automorphisms.
-/

public section

namespace Held.AutomorphismLocalPair
open Subgroup LocalPairs.SylowGeometry.Calculations Theory.GroupTheory

/-- The actual local equivalence induced by a conjugacy of the marked Sylow subgroup. -/
noncomputable def largeLocalEquivOfConjugate (T : Sylow 2 He) (g : He)
    (hg : representative.map (MulAut.conj g).toMonoidHom = (T : Subgroup He)) :
    representativeLargeLocal ≃* largeLocal T :=
  (representativeLargeLocal.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr (by
      rw [← representative_largeLocal, ← largeLocal_map, hg]))

/-- The local equivalence retains the literal ambient conjugation map. -/
@[simp] theorem coe_largeLocalEquivOfConjugate (T : Sylow 2 He) (g : He)
    (hg : representative.map (MulAut.conj g).toMonoidHom = (T : Subgroup He))
    (x : representativeLargeLocal) :
    (largeLocalEquivOfConjugate T g hg x : He) = g * (x : He) * g⁻¹ := by
  rfl

/-- Apply the two independent calculations to the unchanged representative normalizer. -/
theorem representative_subnormal_orders_of_calculations
    (hnine : Nat.card (pResidual 2 representativeLargeLocal ⧸
      pCore 2 (pResidual 2 representativeLargeLocal)) = 9)
    (hcubic : ∀ x : representativeLargeLocal, orderOf x = 3 →
      12 < Nat.card (⁅representativeLargeKernel, zpowers x⁆ :
        Subgroup representativeLargeLocal))
    (E : Subgroup representativeLargeLocal) (hE : E.IsSubnormal)
    (hp : IsPPerfect 2 E) :
    Nat.card E = 1 ∨
      (Nat.card (E ⧸ pCore 2 E) = 3 ∧ 12 < Nat.card E) ∨
        Nat.card (E ⧸ pCore 2 E) = 9 :=
  subnormal_orders_of_residual_nine_of_cubic_commutators representativeLargeKernel
    representativeLargeKernel_isPGroup hnine hcubic E hE hp

/-- Conditional native consumer, retaining relative subnormality and intrinsic quotients. -/
theorem subnormal_largeLocal_orders_of_calculations
    (hnine : Nat.card (pResidual 2 representativeLargeLocal ⧸
      pCore 2 (pResidual 2 representativeLargeLocal)) = 9)
    (hcubic : ∀ x : representativeLargeLocal, orderOf x = 3 →
      12 < Nat.card (⁅representativeLargeKernel, zpowers x⁆ :
        Subgroup representativeLargeLocal))
    (T : Sylow 2 He) (E : Subgroup (largeLocal T))
    (hE : E.IsSubnormal) (hp : IsPPerfect 2 E) :
    Nat.card E = 1 ∨
      (Nat.card (E ⧸ pCore 2 E) = 3 ∧ 12 < Nat.card E) ∨
        Nat.card (E ⧸ pCore 2 E) = 9 := by
  obtain ⟨g, hg⟩ := exists_conjugate_representative T
  let e := (largeLocalEquivOfConjugate T g hg).symm
  let D := E.map e.toMonoidHom
  let eE : E ≃* D := e.subgroupMap E
  have hD : D.IsSubnormal := hE.map e.surjective
  have hpD : IsPPerfect 2 D := hp.of_surjective eE.toMonoidHom eE.surjective
  have hc := Nat.card_congr eE.toEquiv
  have hq := Nat.card_congr (QuotientGroup.congr _ _ eE (pCore_map_iso 2 eE)).toEquiv
  rw [hc, hq]
  exact representative_subnormal_orders_of_calculations hnine hcubic D hD hpD

/-- The certified finite calculations give the order restriction in the full
normalizer of the literal join `ambient 20 ⊔ ambient 21`. -/
theorem representative_subnormal_orders
    (E : Subgroup representativeLargeLocal) (hE : E.IsSubnormal)
    (hp : IsPPerfect 2 E) :
    Nat.card E = 1 ∨
      (Nat.card (E ⧸ pCore 2 E) = 3 ∧ 12 < Nat.card E) ∨
        Nat.card (E ⧸ pCore 2 E) = 9 :=
  representative_subnormal_orders_of_calculations
    representative_residual_core_quotient_card
    (representative_large_cubic_commutator_bound representative_residual_core_quotient_card)
    E hE hp

/-- Every relatively subnormal two-perfect subgroup of the canonical large
Held local has the stated intrinsic core-quotient order, and the cubic branch
has order strictly greater than twelve. No additional model premise remains. -/
theorem subnormal_largeLocal_orders
    (T : Sylow 2 He) (E : Subgroup (largeLocal T))
    (hE : E.IsSubnormal) (hp : IsPPerfect 2 E) :
    Nat.card E = 1 ∨
      (Nat.card (E ⧸ pCore 2 E) = 3 ∧ 12 < Nat.card E) ∨
        Nat.card (E ⧸ pCore 2 E) = 9 :=
  subnormal_largeLocal_orders_of_calculations
    representative_residual_core_quotient_card
    (representative_large_cubic_commutator_bound representative_residual_core_quotient_card)
    T E hE hp

end Held.AutomorphismLocalPair
