module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic.Group

/-!
# A commutator homomorphism into a subgroup quotient

If `[X,u] ≤ W` and `[W X,W X] ≤ E`, the map `x ↦ [x,u]E` is a
homomorphism from X to the literal quotient W/E. The product defect is
`[x,[y,u]] [[y,u],[x,u]]`, which lies in E. Neither ambient normality
of E nor a commutative ambient group is required.

This is the commutator map used in Aschbacher–Smith, Lemma 12.8.9,
printed p.853, combined manuscript of 1 March 2004.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

/-- The source commutator map, with codomain the actual quotient W/E. -/
def commutatorQuotientHom (X W E : Subgroup G)
    [(E.subgroupOf W).Normal] (u : G)
    (hcomm : ∀ x ∈ X, ⁅x, u⁆ ∈ W)
    (habel : ⁅W ⊔ X, W ⊔ X⁆ ≤ E) : X →* W ⧸ E.subgroupOf W where
  toFun x := QuotientGroup.mk' (E.subgroupOf W) ⟨⁅(x : G), u⁆, hcomm x x.property⟩
  map_one' := by
    apply (QuotientGroup.eq_one_iff _).mpr
    change ⁅(1 : G), u⁆ ∈ E
    simp
  map_mul' x y := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    change ⁅(x : G) * y, u⁆ / (⁅(x : G), u⁆ * ⁅(y : G), u⁆) ∈ E
    have he : ⁅(x : G) * y, u⁆ / (⁅(x : G), u⁆ * ⁅(y : G), u⁆) =
        ⁅(x : G), ⁅(y : G), u⁆⁆ * ⁅⁅(y : G), u⁆, ⁅(x : G), u⁆⁆ := by
      simp only [commutatorElement_def, div_eq_mul_inv]
      group
    rw [he]
    exact E.mul_mem
      (habel (commutator_mem_commutator ((le_sup_right : X ≤ W ⊔ X) x.property)
        ((le_sup_left : W ≤ W ⊔ X) (hcomm y y.property))))
      (habel (commutator_mem_commutator ((le_sup_left : W ≤ W ⊔ X) (hcomm y y.property))
        ((le_sup_left : W ≤ W ⊔ X) (hcomm x x.property))))

@[simp] theorem commutatorQuotientHom_apply (X W E : Subgroup G)
    [(E.subgroupOf W).Normal] (u : G)
    (hcomm : ∀ x ∈ X, ⁅x, u⁆ ∈ W) (habel : ⁅W ⊔ X, W ⊔ X⁆ ≤ E) (x : X) :
    commutatorQuotientHom X W E u hcomm habel x =
      QuotientGroup.mk' (E.subgroupOf W) ⟨⁅(x : G), u⁆, hcomm x x.property⟩ := rfl

/-- The kernel calculation needs no unstated choice of quotient coordinates. -/
theorem mem_commutatorQuotientHom_ker (X W E : Subgroup G)
    [(E.subgroupOf W).Normal] (u : G)
    (hcomm : ∀ x ∈ X, ⁅x, u⁆ ∈ W) (habel : ⁅W ⊔ X, W ⊔ X⁆ ≤ E) (x : X) :
    x ∈ (commutatorQuotientHom X W E u hcomm habel).ker ↔ ⁅(x : G), u⁆ ∈ E := by
  exact QuotientGroup.eq_one_iff _

/-- Pulling a subgroup image back through the commutator map is the literal
ambient membership condition in ZE. -/
theorem commutatorQuotientHom_mem_image_iff (X W E Z : Subgroup G)
    [(E.subgroupOf W).Normal] (u : G)
    (hcomm : ∀ x ∈ X, ⁅x, u⁆ ∈ W) (habel : ⁅W ⊔ X, W ⊔ X⁆ ≤ E)
    (hEW : E ≤ W) (hZW : Z ≤ W) (x : X) :
    commutatorQuotientHom X W E u hcomm habel x ∈
      (Z.subgroupOf W).map (QuotientGroup.mk' (E.subgroupOf W)) ↔
      ⁅(x : G), u⁆ ∈ Z ⊔ E := by
  change (⟨⁅(x : G), u⁆, hcomm x x.property⟩ : W) ∈
    ((Z.subgroupOf W).map (QuotientGroup.mk' (E.subgroupOf W))).comap
      (QuotientGroup.mk' (E.subgroupOf W)) ↔ _
  rw [comap_map_eq, QuotientGroup.ker_mk']
  rw [← subgroupOf_sup hZW hEW]
  rfl

end Subgroup
