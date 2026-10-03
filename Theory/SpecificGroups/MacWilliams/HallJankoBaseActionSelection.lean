module

public import Theory.SpecificGroups.MacWilliams.HallJankoBaseActions
public import Theory.GroupAction.C4SquareHallJankoActions
public import Theory.GroupTheory.PGroup.C4SquareConjugationImage
public import Theory.GroupTheory.PGroup.NormalFourElementaryCentralizer

/-!
# Lifting selected Hall–Janko automorphisms

Once the finite action problem supplies a basis and the six automorphism
identities, taking preimages in the elementary subgroup and the ambient
group gives the required base actions. The basis and its omega subgroup
are transported by the subgroup inclusion. No generation or relations
between the lifts are needed for this step.

The intrinsic existence of the automorphism data is a separate remaining
selection problem. Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3(a),
printed p.386, citing MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3.
-/

open Subgroup
namespace MacWilliamsSylow

/-- Lift a selected automorphism frame through the actual conjugation map. -/
public theorem baseActions_of_autActions
    {P : Type*} [Group P] (D W B : Subgroup P) [D.Normal]
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (f : C4SquareExtension.HallJankoAutActions
      ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range
      (MulAut.conjNormal : P →* MulAut D).range) :
    Nonempty (HallJankoBaseActions D W B) := by
  obtain ⟨u, hu⟩ := f.u_mem
  obtain ⟨v, hv⟩ := f.v_mem
  obtain ⟨t, ht⟩ := f.t_mem
  refine ⟨{
    a := f.a, b := f.b, u := u, v := v, t := t
    a_four := congrArg D.subtype f.a_four
    b_four := congrArg D.subtype f.b_four
    ba := congrArg D.subtype f.ba
    base := ?_, four := ?_
    u_mem := u.property, v_mem := v.property
    ua := ?_, ub := ?_, va := ?_, vb := ?_, ta := ?_, tb := ?_ }⟩
  · have hh := congrArg (Subgroup.map D.subtype) f.base
    rw [← MonoidHom.range_eq_map, range_subtype] at hh
    simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      Subgroup.subtype_apply] using hh.symm
  · rw [← hO, f.four, MonoidHom.map_closure]
    simp only [Set.image_insert_eq, Set.image_singleton, map_pow, Subgroup.subtype_apply]
  · have hh := congrArg (fun a : D => (a : P)) f.ua
    rw [← hu] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · have hh := congrArg (fun a : D => (a : P)) f.ub
    rw [← hu] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · have hh := congrArg (fun a : D => (a : P)) f.va
    rw [← hv] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · have hh := congrArg (fun a : D => (a : P)) f.vb
    rw [← hv] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · have hh := congrArg (fun a : D => (a : P)) f.ta
    rw [← ht] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · have hh := congrArg (fun a : D => (a : P)) f.tb
    rw [← ht] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh

end MacWilliamsSylow
