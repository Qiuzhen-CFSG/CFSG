module

public import Theory.GroupAction.CentralKernelFixedResidual

/-!
# Compatible transport of fixed subgroups and their residuals

A multiplicative equivalence intertwining two automorphisms restricts to
an equivalence of their fixed subgroups and then of their p-residuals.
The accompanying equations retain the ambient elements. In particular,
changing a representative by an actual compatible conjugation preserves
these models, without any assertion about simultaneous conjugacy of a pair.

Application: the chosen graph and field representatives in Aschbacher--Smith
15.3.38, printed pp.1136--1137 (1 March 2004 manuscript).
-/

public section

namespace MulAut
open Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- A compatible equivalence restricts to the actual fixed subgroups. -/
noncomputable def fixedSubgroupEquivOfCompatible (e : G ≃* H)
    (a : MulAut G) (b : MulAut H) (heq : ∀ x, e (a x) = b (e x)) :
    a.fixedSubgroup ≃* b.fixedSubgroup :=
  MulEquiv.ofBijective (fixedSubgroupMap a b e.toMonoidHom heq) (by
    constructor
    · intro x y h
      exact Subtype.ext (e.injective (congrArg (fun z : b.fixedSubgroup => (z : H)) h))
    · intro y
      refine ⟨⟨e.symm y, ?_⟩, ?_⟩
      · rw [mem_fixedSubgroup]
        apply e.injective
        rw [heq, e.apply_symm_apply, (mem_fixedSubgroup _ _).mp y.property]
      · exact Subtype.ext (e.apply_symm_apply y))

/-- Fixed-subgroup transport retains the specified ambient equivalence. -/
@[simp] theorem fixedSubgroupEquivOfCompatible_apply (e : G ≃* H)
    (a : MulAut G) (b : MulAut H) (heq : ∀ x, e (a x) = b (e x))
    (x : a.fixedSubgroup) :
    (fixedSubgroupEquivOfCompatible e a b heq x : H) = e x := by
  unfold fixedSubgroupEquivOfCompatible
  rfl

/-- Restriction to p-residuals requires no finiteness hypothesis. -/
noncomputable def fixedResidualEquivOfCompatible (p : ℕ) (e : G ≃* H)
    (a : MulAut G) (b : MulAut H) (heq : ∀ x, e (a x) = b (e x)) :
    pResidual p a.fixedSubgroup ≃* pResidual p b.fixedSubgroup := by
  let d := fixedSubgroupEquivOfCompatible e a b heq
  exact ((pResidual p _).equivMapOfInjective d.toMonoidHom d.injective).trans
    (MulEquiv.subgroupCongr (map_pResidual p d))

/-- Residual transport retains the same ambient equivalence. -/
@[simp] theorem fixedResidualEquivOfCompatible_apply (p : ℕ) (e : G ≃* H)
    (a : MulAut G) (b : MulAut H) (heq : ∀ x, e (a x) = b (e x))
    (x : pResidual p a.fixedSubgroup) :
    (((fixedResidualEquivOfCompatible p e a b heq x : pResidual p b.fixedSubgroup) :
      b.fixedSubgroup) : H) = e ((x : a.fixedSubgroup) : G) := by
  unfold fixedResidualEquivOfCompatible
  exact fixedSubgroupEquivOfCompatible_apply e a b heq x.val

end MulAut
