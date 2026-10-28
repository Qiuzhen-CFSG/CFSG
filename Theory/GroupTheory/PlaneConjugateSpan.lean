module
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.CommutatorPreimage
public import Mathlib.GroupTheory.Index

/-!
# A plane span with a fixed line

A group preserving a four-group and its involution subgroup acts trivially
on the quotient of order two. If a normal actor preserves the seed plane,
its commutator bound therefore extends to the whole conjugate span through
the invariant commutator preimage.

Source application: Aschbacher--Smith, 14.6.10(5), printed p.1029; the
four-dimensional exceptional A7 branch uses this bound for the second
parabolic's two-core.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

theorem plane_line_commutator (V Z R : Subgroup G) (hZV : Z ≤ V)
    (hV : Nat.card V = 4) (hZ : Nat.card Z = 2)
    (hRV : R ≤ normalizer (V : Set G)) (hRZ : R ≤ normalizer (Z : Set G)) :
    ⁅V,R⁆ ≤ Z := by
  have hi : (Z.subgroupOf V).index = 2 := by
    have hc := (Z.subgroupOf V).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hZV).toEquiv,hZ,hV] at hc
    omega
  rw [commutator_comm]
  apply commutator_le.mpr
  intro r hr v hv
  let w : V := ⟨r*v*r⁻¹,le_normalizer_iff.mp hRV r hr v hv⟩
  let x : V := ⟨v,hv⟩
  have hh : w*x⁻¹ ∈ Z.subgroupOf V := by
    apply (Subgroup.mul_mem_iff_of_index_two hi).mpr
    rw [inv_mem_iff]
    exact (mem_normalizer_iff.mp (hRZ hr) v).symm
  exact hh

theorem plane_span_commutator (V Z W J R : Subgroup G)
    (hVW : V ≤ W) (hZV : Z ≤ V) (hV : Nat.card V = 4) (hZ : Nat.card Z = 2)
    (hRV : R ≤ normalizer (V : Set G))
    (hWZ : W ≤ normalizer (Z : Set G))
    (hJW : J ≤ normalizer (W : Set G)) (hJR : J ≤ normalizer (R : Set G))
    (hJZ : J ≤ normalizer (Z : Set G)) (hRJ : R ≤ J) :
    ⁅conjugateSpanBy V J,R⁆ ≤ Z := by
  have hVP := le_commutatorPreimage hVW
    (plane_line_commutator V Z R hZV hV hZ hRV (hRJ.trans hJZ))
  exact (commutator_mono
    (conjugateSpanBy_le hVP (commutatorPreimage_normalized W R Z J hWZ hJW hJR hJZ))
    le_rfl).trans (commutator_commutatorPreimage_le W R Z hWZ)
end Subgroup
