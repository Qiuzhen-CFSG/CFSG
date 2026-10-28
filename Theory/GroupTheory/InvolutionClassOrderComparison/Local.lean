module
public import Theory.GroupTheory.InvolutionClassOrderComparison

/-!
# Thompson fibers in an involution-containing part of a centralizer

An odd extension of a centralizer need not change its mixed-involution fibers.
It suffices to mark a subgroup containing all its involutions, provided the
marking preserves the two ambient conjugacy classes and the distinguished
involution. This form of the comparison applies to the cubic triality endpoints.

Source: the mixed-pair proof of Aschbacher--Smith F.4.43, printed p.296.
-/

public noncomputable section
namespace Theory.GroupTheory.InvolutionClassOrderComparison
open Subgroup TwoInvolutionClassOrder
variable {G K : Type*} [Group G] [Finite G] [Group K] [Finite K]

omit [Finite G] in
private theorem conj_order {x y : G} (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨g,rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq x).symm

/-- Compare the actual fibers using only the part of the source centralizer
containing all its involutions. The conjugacy conditions are ambient. -/
def fiberEquivOfLocalCentralizer (A : Subgroup G) (z v : G) (u : A)
    (z' v' u' : K)
    (hz : orderOf z = 2) (hv : orderOf v = 2) (hn : ¬ IsConj z v)
    (hz' : orderOf z' = 2) (hv' : orderOf v' = 2) (hn' : ¬ IsConj z' v')
    (hlocal : ∀ x ∈ centralizer ({(u : G)} : Set G), orderOf x = 2 → x ∈ A)
    (e : A ≃* centralizer ({u'} : Set K)) (he : (e u : K) = u')
    (hfz : ∀ a : A, IsConj z (a : G) ↔ IsConj z' (e a : K))
    (hfv : ∀ a : A, IsConj v (a : G) ↔ IsConj v' (e a : K)) :
    Fiber z v (u : G) ≃ Fiber z' v' u' where
  toFun p := by
    have hc := fiber_mem_centralizer hz hv hn p
    let a : A := ⟨p.val.1,hlocal _ hc.1 ((conj_order p.property.1).symm.trans hz)⟩
    let b : A := ⟨p.val.2,hlocal _ hc.2 ((conj_order p.property.2.1).symm.trans hv)⟩
    have hh : halfOrder a b = u := Subtype.ext
      ((halfOrder_coe A a b).trans p.property.2.2)
    refine ⟨((e a : K),(e b : K)),(hfz a).mp p.property.1,
      (hfv b).mp p.property.2.1,?_⟩
    rw [←halfOrder_coe,halfOrder_map,hh,he]
  invFun p := by
    have hc := fiber_mem_centralizer hz' hv' hn' p
    let a : centralizer ({u'} : Set K) := ⟨p.val.1,hc.1⟩
    let b : centralizer ({u'} : Set K) := ⟨p.val.2,hc.2⟩
    have hh : halfOrder a b = e u := Subtype.ext
      ((halfOrder_coe _ a b).trans (p.property.2.2.trans he.symm))
    refine ⟨((e.symm a : G),(e.symm b : G)),
      (hfz _).mpr (by simpa only [e.apply_symm_apply] using p.property.1),
      (hfv _).mpr (by simpa only [e.apply_symm_apply] using p.property.2.1),?_⟩
    rw [←halfOrder_coe,halfOrder_map,hh,e.symm_apply_apply]
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> exact congrArg Subtype.val (e.symm_apply_apply _)
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> exact congrArg Subtype.val (e.apply_symm_apply _)

/-- The Thompson count is unchanged by such a local centralizer marking. -/
theorem kappa_eq_of_localCentralizer (A : Subgroup G) (z v : G) (u : A)
    (z' v' u' : K)
    (hz : orderOf z = 2) (hv : orderOf v = 2) (hn : ¬ IsConj z v)
    (hz' : orderOf z' = 2) (hv' : orderOf v' = 2) (hn' : ¬ IsConj z' v')
    (hlocal : ∀ x ∈ centralizer ({(u : G)} : Set G), orderOf x = 2 → x ∈ A)
    (e : A ≃* centralizer ({u'} : Set K)) (he : (e u : K) = u')
    (hfz : ∀ a : A, IsConj z (a : G) ↔ IsConj z' (e a : K))
    (hfv : ∀ a : A, IsConj v (a : G) ↔ IsConj v' (e a : K)) :
    kappa z v (u : G) = kappa z' v' u' := by
  simp only [kappa_def,←halfOrder_def]
  exact Nat.card_congr (fiberEquivOfLocalCentralizer A z v u z' v' u'
    hz hv hn hz' hv' hn' hlocal e he hfz hfv)

end Theory.GroupTheory.InvolutionClassOrderComparison
