module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Fusion.Count.LocalOrbit.GridCoordinates
public import Theory.GroupAction.SymmetricThreeDiagonalGrid

/-!
# The outside action on each quaternion factor

Each action of H/Q on the three axes contains a cubic. An endomorphism of
S₃ with a cubic image is inner, so both factor actions are faithful. An
outside element therefore cannot act by an inner automorphism on either
quaternion factor. Normality throughout is relative to H = C_G(b).

This supplies the outside action used in Aschbacher, “A 2-local
characterization of M12”, Lemma 4.8, p.41, from the local hypotheses of
Lemmas 2.2–2.3. No ambient recognition is used.
-/

open Subgroup Theory.GroupTheory Subgroup.QuaternionCentralProductData
open scoped IsMulCommutative
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.QuaternionExchange
variable {G : Type*} [Group G] [Finite G] {b : G}

private theorem factorAction_injective (h : Hypotheses b) (hn : QuaternionSubgroupsNormal b)
    (q : QuaternionCentralProductData (Core b))
    (R : Subgroup (Core b)) (hR : R = q.left ∨ R = q.right) :
    Function.Injective (h.localOrbit_factorAction hn q R hR) := by
  let e := h.quotient_model.some
  let c := q.factorPointsEquivFin R hR
  let f := h.localOrbit_factorAction hn q R hR
  let g := c.permCongrHom.toMonoidHom.comp (f.comp e.symm.toMonoidHom)
  have hthree : ∃ a, orderOf (g a) = 3 := by
    obtain ⟨a, ha⟩ := h.localOrbit_factorAction_three hn q R hR
    refine ⟨e a, ?_⟩
    change orderOf (c.permCongrHom (f (e.symm (e a)))) = 3
    rw [e.symm_apply_apply, c.permCongrHom.orderOf_eq, ha]
  obtain ⟨t, ht⟩ := Theory.GroupAction.SymmetricThreeDiagonalGrid.endomorphism_inner g hthree
  intro x y hxy
  apply e.injective
  apply (MulAut.conj t).injective
  change t * e x * t⁻¹ = t * e y * t⁻¹
  rw [← ht, ← ht]
  change c.permCongrHom (f (e.symm (e x))) = c.permCongrHom (f (e.symm (e y)))
  rw [e.symm_apply_apply, e.symm_apply_apply, hxy]

/-- An element outside the intrinsic core acts outerly on either factor. -/
public theorem factor_outer (h : Hypotheses b) (hn : QuaternionSubgroupsNormal b)
    (q : QuaternionCentralProductData (Core b))
    (R : Subgroup (Core b)) (hR : R = q.left ∨ R = q.right)
    (u : Centralizer b) (hu : u ∉ Core b) :
    ¬ ∃ v : R, ∀ x : R, MulAut.conjNormal u (x : Core b) =
      (v : Core b) * x * (v : Core b)⁻¹ := by
  rintro ⟨v, hv⟩
  have htriv : h.localOrbit_factorAction hn q R hR (QuotientGroup.mk' (Core b) u) = 1 := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    rw [h.localOrbit_factorAction_mk_val]
    obtain ⟨w, hw, he⟩ := x.val.property
    change quotientAut (center (Core b)) (MulAut.conjNormal u) x.val.val = x.val.val
    rw [← he, quotientAut_apply_mk, hv ⟨w, hw⟩]
    let := q.quotient_elementary
    simp only [map_mul, map_inv]
    rw [mul_comm (QuotientGroup.mk' (center (Core b)) (v : Core b)), mul_inv_cancel_right]
  have heq : QuotientGroup.mk' (Core b) u = 1 :=
    factorAction_injective h hn q R hR (htriv.trans (map_one _).symm)
  exact hu ((QuotientGroup.eq_one_iff u).mp heq)
end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.QuaternionExchange
