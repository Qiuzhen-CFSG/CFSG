module
public import Theory.GroupTheory.PerfectCentralCoverInnerLift
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Compatible actions through perfect central covers

An equivariant surjection with central kernel detects identity and inner
actors when its domain is perfect. The actual actor homomorphisms therefore
have equal kernels, equal element orders, and equal outer-action kernels
and orders. The kernel need not be the whole center or characteristic:
only the displayed equivariance is used.

Source application: the core-to-star comparison in Aschbacher--Smith C.2.7
and original 14.6.15, printed pp.145--147 and 1035.
-/

public section
namespace PerfectCentralCovering
open Subgroup
variable {E B A : Type*} [Group E] [Group B] [Group A]

/-- A compatible quotient actor is trivial exactly when its lift is trivial. -/
theorem Cover.equivariant_eq_one_iff (f : Cover E B)
    (a : MulAut E) (b : MulAut B)
    (he : ∀ x, f.toMonoidHom (a x) = b (f.toMonoidHom x)) :
    a = 1 ↔ b = 1 := by
  constructor
  · intro ha
    ext y
    obtain ⟨x,rfl⟩ := f.surjective y
    exact (he x).symm.trans (congrArg f.toMonoidHom (DFunLike.congr_fun ha x))
  · intro hb
    let := f.isPerfect
    apply MulEquiv.toMonoidHom_injective
    apply monoidHom_eq_of_isPerfect_of_comp_eq f.toMonoidHom f.ker_le_center
    ext x
    exact (he x).trans (DFunLike.congr_fun hb (f.toMonoidHom x))

/-- The original central projection preserves and reflects innerness. -/
theorem Cover.equivariant_inner_iff (f : Cover E B)
    (a : MulAut E) (b : MulAut B)
    (he : ∀ x, f.toMonoidHom (a x) = b (f.toMonoidHom x)) :
    a ∈ MulAut.innerSubgroup E ↔ b ∈ MulAut.innerSubgroup B := by
  constructor
  · rintro ⟨x,rfl⟩
    refine ⟨f.toMonoidHom x,?_⟩
    ext y
    obtain ⟨z,rfl⟩ := f.surjective y
    rw [←he]
    simp only [MulAut.conj_apply,map_mul,map_inv]
  · rintro ⟨y,hy⟩
    obtain ⟨x,hx⟩ := f.inner_of_equivariant_inner a b he ⟨y,hy.symm⟩
    exact ⟨x,hx.symm⟩

variable (f : Cover E B) (a : A →* MulAut E) (b : A →* MulAut B)
    (he : ∀ g x, f.toMonoidHom (a g x) = b g (f.toMonoidHom x))

include f he in
/-- Compatible actions have exactly the same kernel in their actor group. -/
theorem Cover.equivariantActions_ker : a.ker = b.ker := by
  ext g
  exact f.equivariant_eq_one_iff (a g) (b g) (he g)

include f he in
/-- Every actor has the same order on the cover and quotient. -/
theorem Cover.equivariantActions_order (g : A) : orderOf (a g) = orderOf (b g) := by
  apply orderOf_eq_orderOf_iff.mpr
  intro n
  rw [←map_pow,←map_pow]
  exact f.equivariant_eq_one_iff (a (g^n)) (b (g^n)) (he (g^n))

include f he in
/-- The outer-action kernels agree under the same projection. -/
theorem Cover.equivariantActions_outer_ker :
    ((QuotientGroup.mk' (MulAut.innerSubgroup E)).comp a).ker =
      ((QuotientGroup.mk' (MulAut.innerSubgroup B)).comp b).ker := by
  ext g
  change QuotientGroup.mk' _ (a g) = 1 ↔ QuotientGroup.mk' _ (b g) = 1
  exact (QuotientGroup.eq_one_iff (a g)).trans
    ((f.equivariant_inner_iff (a g) (b g) (he g)).trans
      (QuotientGroup.eq_one_iff (b g)).symm)

include f he in
/-- The actual outer classes of an actor have equal orders. -/
theorem Cover.equivariantActions_outer_order (g : A) :
    orderOf (QuotientGroup.mk' (MulAut.innerSubgroup E) (a g)) =
      orderOf (QuotientGroup.mk' (MulAut.innerSubgroup B) (b g)) := by
  apply orderOf_eq_orderOf_iff.mpr
  intro n
  rw [←map_pow,←map_pow,←map_pow,←map_pow]
  exact (QuotientGroup.eq_one_iff (a (g^n))).trans
    ((f.equivariant_inner_iff (a (g^n)) (b (g^n)) (he (g^n))).trans
      (QuotientGroup.eq_one_iff (b (g^n))).symm)
end PerfectCentralCovering
