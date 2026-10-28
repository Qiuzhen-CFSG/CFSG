module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.Models

/-!
# Transport of the second-centralizer mixed-pair count

Every pair in the ambient Thompson fiber lies in the full centralizer of its
half-order involution. An actual marked isomorphism transports that fiber to
`ModelFiber`, retaining the ambient classes. Two-class coverage determines the
second marking from the first; no internal fusion-control premise is used.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 1.2 and 4.2–4.3.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
open Subgroup Theory.GroupTheory.TwoInvolutionClassOrder
variable {G : Type*} [Group G] [Finite G] {z t : G} {n : ℕ}

omit [Finite G] in
public theorem MarkedModel.second (m : MarkedModel z t n) (ht : orderOf t = 2)
    (hnt : ¬ IsConj z t)
    (hc : ∀ x : G, orderOf x = 2 → IsConj z x ∨ IsConj t x)
    (x : Centralizer t) : IsConj t (x : G) ↔ SecondClass (m.equiv x) := by
  have ho : orderOf (m.equiv x) = orderOf (x : G) :=
    (m.equiv.orderOf_eq x).trans (Subgroup.orderOf_coe x).symm
  constructor
  · intro hx
    have hxorder : orderOf (x : G) = 2 := by
      obtain ⟨g, hg⟩ := isConj_iff.mp hx
      rw [← hg]
      exact ((MulAut.conj g).orderOf_eq t).trans ht
    refine ⟨ho.trans hxorder, ?_⟩
    intro hf
    exact hnt (((m.first x).mpr hf).trans hx.symm)
  · rintro ⟨hx, hf⟩
    exact (hc x (ho.symm.trans hx)).resolve_left (fun h => hf ((m.first x).mp h))

public noncomputable def MarkedModel.fiberEquiv (m : MarkedModel z t n)
    (hz : orderOf z = 2) (ht : orderOf t = 2) (hnt : ¬ IsConj z t)
    (hc : ∀ x : G, orderOf x = 2 → IsConj z x ∨ IsConj t x) :
    Fiber z t t ≃ ModelFiber n where
  toFun p := by
    have hp := fiber_mem_centralizer hz ht hnt p
    let x : Centralizer t := ⟨p.val.1, hp.1⟩
    let y : Centralizer t := ⟨p.val.2, hp.2⟩
    refine ⟨(m.equiv x, m.equiv y), (m.first x).mp p.property.1,
      (m.second ht hnt hc y).mp p.property.2.1, ?_⟩
    rw [halfOrder_map]
    have he : halfOrder x y = distinguished t :=
      Subtype.ext ((halfOrder_coe (Centralizer t) x y).trans p.property.2.2)
    exact (congrArg m.equiv he).trans m.central
  invFun p := by
    let x := m.equiv.symm p.val.1
    let y := m.equiv.symm p.val.2
    have hx : IsConj z (x : G) := (m.first x).mpr (by simpa [x] using p.property.1)
    have hy : IsConj t (y : G) :=
      (m.second ht hnt hc y).mpr (by simpa [y] using p.property.2.1)
    refine ⟨((x : G), (y : G)), hx, hy, ?_⟩
    have he : halfOrder x y = distinguished t := by
      apply m.equiv.injective
      rw [← halfOrder_map, m.central]
      simpa [x, y] using p.property.2.2
    exact (halfOrder_coe (Centralizer t) x y).symm.trans (congrArg Subtype.val he)
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext (congrArg Subtype.val (m.equiv.symm_apply_apply _))
      (congrArg Subtype.val (m.equiv.symm_apply_apply _))
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext (m.equiv.apply_symm_apply _) (m.equiv.apply_symm_apply _)

public theorem MarkedModel.kappa_eq (m : MarkedModel z t n)
    (hz : orderOf z = 2) (ht : orderOf t = 2) (hnt : ¬ IsConj z t)
    (hc : ∀ x : G, orderOf x = 2 → IsConj z x ∨ IsConj t x) :
    kappa z t t = Nat.card (ModelFiber n) := by
  rw [kappa_def]
  simpa only [Fiber, halfOrder_def] using Nat.card_congr (m.fiberEquiv hz ht hnt hc)

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
