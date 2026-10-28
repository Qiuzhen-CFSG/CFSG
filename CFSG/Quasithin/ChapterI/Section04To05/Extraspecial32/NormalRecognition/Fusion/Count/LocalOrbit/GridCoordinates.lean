module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Fusion.Count.LocalOrbit.Action
public import Theory.GroupTheory.QuaternionCentralProductSingularGrid

/-!
# Equivariant singular grid under relative quaternion normality

Relative normality preserves the two actual quaternion factors of the core.
Their central quotient images are therefore preserved by the literal H/Q
outer action, which restricts to permutation actions on their three nonidentity
points. Multiplication supplies the singular-coset coordinates and proves their
equivariance with the canonical centralizer action.

Both factor actions contain a cubic. If a generator of the source Sylow
three-subgroup acted trivially on either factor quotient, its cubic action
would fix that quaternion factor pointwise. The source equality C_Q(X) = ⟨z⟩
would then put a group of order eight in the center of order two.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 2.2–2.3, especially 2.3(2)(b); Aschbacher–Smith,
I.4.6, printed p.417, `refs/quasithin.pdf`.
-/

namespace CFSG.Quasithin.Extraspecial32
open Subgroup Theory.GroupTheory Subgroup.QuaternionCentralProductData
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace Hypotheses

public theorem localOrbit_factorQuotient_preserved (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : QuaternionCentralProductData (Core z))
    (R : Subgroup (Core z)) (hR : R = d.left ∨ R = d.right)
    (a : Centralizer z ⧸ Core z) :
    (factorQuotient R).map (h.localOrbit_outerAction a).toMonoidHom = factorQuotient R := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Core z) a
  rw [h.localOrbit_outerAction_mk]
  change (R.map (QuotientGroup.mk' (center (Core z)))).map
    (quotientAut (center (Core z)) (MulAut.conjNormal a)).toMonoidHom = _
  rw [map_map]
  have he : (quotientAut (center (Core z)) (MulAut.conjNormal a)).toMonoidHom.comp
      (QuotientGroup.mk' (center (Core z))) =
      (QuotientGroup.mk' (center (Core z))).comp (MulAut.conjNormal a).toMonoidHom := by
    ext x
    exact quotientAut_apply_mk _ _ _
  rw [he, ← map_map]
  rcases hR with rfl | rfl
  · rw [(h.localOrbit_factor_preserved hn d a).1]
  · rw [(h.localOrbit_factor_preserved hn d a).2]

public def localOrbit_factorAction (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : QuaternionCentralProductData (Core z))
    (R : Subgroup (Core z)) (hR : R = d.left ∨ R = d.right) :
    (Centralizer z ⧸ Core z) →* Equiv.Perm (FactorPoints R) :=
  factorPointAction R h.localOrbit_outerAction (h.localOrbit_factorQuotient_preserved hn d R hR)

@[simp] public theorem localOrbit_factorAction_mk_val (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : QuaternionCentralProductData (Core z))
    (R : Subgroup (Core z)) (hR : R = d.left ∨ R = d.right)
    (a : Centralizer z) (v : FactorPoints R) :
    ((h.localOrbit_factorAction hn d R hR (QuotientGroup.mk' (Core z) a) v).val :
      Core z ⧸ center (Core z)) =
      quotientAut (center (Core z)) (MulAut.conjNormal a) v.val := by
  rw [localOrbit_factorAction, factorPointAction_val, h.localOrbit_outerAction_mk]
  rfl


public theorem localOrbit_factorAction_three (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : QuaternionCentralProductData (Core z))
    (R : Subgroup (Core z)) (hR : R = d.left ∨ R = d.right) :
    ∃ a, orderOf (h.localOrbit_factorAction hn d R hR a) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := h.X) 3 (by rw [h.sylow_three_card])
  have ha1 : a ≠ 1 := by intro he; simp [he] at ha
  have ha3 : (a : Centralizer z) ^ 3 = 1 := congrArg Subtype.val
    (show a ^ 3 = 1 by simpa only [ha] using pow_orderOf_eq_one a)
  let f := h.localOrbit_factorAction hn d R hR
  refine ⟨QuotientGroup.mk' (Core z) (a : Centralizer z), orderOf_eq_prime ?_ ?_⟩
  · change f (QuotientGroup.mk' (Core z) (a : Centralizer z)) ^ 3 = 1
    rw [← map_pow, ← map_pow, ha3, map_one, map_one]
  · intro htriv
    have hfix (q : R) : MulAut.conjNormal (a : Centralizer z) q.val = q.val := by
      apply d.cubic_fixed_of_quotient_fixed
      · rw [← map_pow, ha3, map_one]
      · let v : factorQuotient R :=
          ⟨QuotientGroup.mk' (center (Core z)) q.val, mem_map_of_mem _ q.property⟩
        by_cases hv : v = 1
        · have hv' : QuotientGroup.mk' (center (Core z)) q.val = 1 := congrArg Subtype.val hv
          rw [hv', map_one]
        · let p : FactorPoints R := ⟨v, hv⟩
          have he := congrArg (fun e : Equiv.Perm (FactorPoints R) =>
            ((e p).val : Core z ⧸ center (Core z))) htriv
          rw [h.localOrbit_factorAction_mk_val] at he
          exact he
    have hle : R ≤ center (Core z) := by
      intro q hq
      have hcomm : Commute (a : Centralizer z) (q : Centralizer z) :=
        mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (hfix ⟨q, hq⟩))
      have hc : (q : Centralizer z) ∈ centralizer (h.X : Set (Centralizer z)) := by
        intro y hy
        obtain ⟨n, hn⟩ := mem_zpowers_iff.mp
          (mem_zpowers_of_prime_card h.sylow_three_card ha1 (g' := (⟨y, hy⟩ : h.X)))
        have hyn : (a : Centralizer z) ^ n = y := congrArg Subtype.val hn
        rw [← hyn]
        exact (hcomm.zpow_left n).eq
      have hz : (q : Centralizer z) ∈ (center (Core z)).map (Core z).subtype := by
        rw [h.core_center_image, ← h.fixed]
        exact ⟨q.property, hc⟩
      obtain ⟨q', hq', he⟩ := hz
      exact (show q' = q from Subtype.ext he) ▸ hq'
    have hc := card_le_of_le hle
    rw [d.center_card, Nat.card_congr (d.factor_model R hR).some.toEquiv,
      show Nat.card (QuaternionGroup 2) = 8 by
        rw [Nat.card_eq_fintype_card, QuaternionGroup.card]] at hc
    omega


/-- The actual singular-coset grid, with both cubic images and no additional premises. -/
public theorem localOrbit_gridModel_of_quaternion_normal (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) : Nonempty (FusionCount.LocalOrbit.GridModel z) := by
  obtain ⟨d⟩ := h.quaternionCentralProduct
  let eL := d.factorPointsEquivFin d.left (Or.inl rfl)
  let eR := d.factorPointsEquivFin d.right (Or.inr rfl)
  let l := h.localOrbit_factorAction hn d d.left (Or.inl rfl)
  let r := h.localOrbit_factorAction hn d d.right (Or.inr rfl)
  let c := d.singularProduct.symm.trans (eL.prodCongr eR)
  refine ⟨{
    left := eL.permCongrHom.toMonoidHom.comp l
    right := eR.permCongrHom.toMonoidHom.comp r
    left_three := ?_
    right_three := ?_
    coordinates := c
    equivariant := ?_ }⟩
  · obtain ⟨a, ha⟩ := h.localOrbit_factorAction_three hn d d.left (Or.inl rfl)
    exact ⟨a, (eL.permCongrHom.orderOf_eq (l a)).trans ha⟩
  · obtain ⟨a, ha⟩ := h.localOrbit_factorAction_three hn d d.right (Or.inr rfl)
    exact ⟨a, (eR.permCongrHom.orderOf_eq (r a)).trans ha⟩
  · intro a v
    let p := d.singularProduct.symm v
    let aq := QuotientGroup.mk' (Core z) a
    have he : d.singularProduct (l aq p.1, r aq p.2) =
        FusionCount.LocalOrbit.cosetAction z a v := by
      have hh := d.singularProduct_natural (MulAut.conjNormal a) p (l aq p.1, r aq p.2)
        (h.localOrbit_factorAction_mk_val hn d d.left (Or.inl rfl) a p.1)
        (h.localOrbit_factorAction_mk_val hn d d.right (Or.inr rfl) a p.2)
      simpa only [p, Equiv.apply_symm_apply, FusionCount.LocalOrbit.cosetAction,
        MonoidHom.comp_apply] using hh
    have hi : d.singularProduct.symm (FusionCount.LocalOrbit.cosetAction z a v) =
        (l aq p.1, r aq p.2) := by rw [← he, Equiv.symm_apply_apply]
    change (eL (d.singularProduct.symm (FusionCount.LocalOrbit.cosetAction z a v)).1,
      eR (d.singularProduct.symm (FusionCount.LocalOrbit.cosetAction z a v)).2) =
      (eL (l aq (eL.symm (eL p.1))), eR (r aq (eR.symm (eR p.2))))
    rw [hi, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end Hypotheses
end CFSG.Quasithin.Extraspecial32
