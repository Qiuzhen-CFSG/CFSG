module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer
/-!
# A relative centralizer bound from abelian commutators

If an element normalizes an abelian subgroup U and its commutators with
X ≤ U lie in W, the commutator map X → W is a homomorphism. Its kernel
is C_X(y), so |X:C_X(y)| ≤ |W|. The controlling subgroup W need not be
contained in U or normal in the ambient group.

Source application: Aschbacher–Smith, 5.1.17, printed p.642: X is the
critical kernel D_H, U is the conjugate span, and W is the endpoint point.
-/

public section
open scoped commutatorElement IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The actual commutator row bounds its centralizer index. -/
theorem centralizer_relIndex_le_card_of_abelian_commutator
    (X U W : Subgroup G) [IsMulCommutative U] (hXU : X ≤ U)
    (y : G) (hy : y ∈ normalizer (U : Set G))
    (hc : ∀ x ∈ X, ⁅x,y⁆ ∈ W) :
    (centralizer ({y} : Set G)).relIndex X ≤ Nat.card W := by
  have hU (x : G) (hx : x ∈ X) : ⁅x,y⁆ ∈ U :=
    (le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hy))
      (commutator_mem_commutator (hXU hx) (mem_zpowers y))
  have hcomm (x z : G) (hx : x ∈ U) (hz : z ∈ U) : x*z = z*x :=
    congrArg Subtype.val (mul_comm (⟨x,hx⟩ : U) ⟨z,hz⟩)
  let f : X →* W := {
    toFun x := ⟨⁅(x : G),y⁆, hc x x.property⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' a b := by
      apply Subtype.ext
      change ⁅(a : G)*(b : G),y⁆ = ⁅(a : G),y⁆ * ⁅(b : G),y⁆
      rw [commutatorElement_mul_left_eq_conj_mul,
        hcomm a _ (hXU a.property) (hU b b.property), mul_inv_cancel_right]
      exact hcomm _ _ (hU b b.property) (hU a a.property) }
  have hk : f.ker = (centralizer ({y} : Set G)).subgroupOf X := by
    ext x
    change (⟨⁅(x : G),y⁆, _⟩ : W) = 1 ↔ _
    rw [Subtype.ext_iff]
    change ⁅(x : G),y⁆ = 1 ↔ (x : G) ∈ centralizer ({y} : Set G)
    rw [commutatorElement_eq_one_iff_mul_comm, mem_centralizer_singleton_iff]
  change ((centralizer ({y} : Set G)).subgroupOf X).index ≤ _
  rw [← hk, index_ker]
  exact Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective
end Subgroup
