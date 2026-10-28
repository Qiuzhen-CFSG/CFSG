module

public import Theory.GroupAction.C4SquareHallJankoActions

/-!
# Transport of the two C₄-square action frames

Conjugating automorphisms along a group isomorphism preserves both the
Hall–Janko and split-inversion frames, including their marked generating
pairs and omega subgroup. This separates the finite coordinate calculation
from the group on which the action was originally given.

Source: the change-of-basis step in Janko–Thompson, Math. Z. 113 (1970),
Theorem 1.3(a), printed p.386, citing MacWilliams,
DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace C4SquareExtension

variable {A B : Type*} [Group A] [Group B]

private theorem pull_apply (e : A ≃* B) (f : MulAut B) (x : B) :
    (MulAut.congr e).symm f (e.symm x) = e.symm (f x) := by
  simp [MulAut.congr]

private theorem pull_mem (e : A ≃* B) (H : Subgroup (MulAut A))
    {f : MulAut B} (hf : f ∈ H.map (MulAut.congr e).toMonoidHom) :
    (MulAut.congr e).symm f ∈ H := by
  obtain ⟨g, hg, rfl⟩ := hf
  change (MulAut.congr e).symm ((MulAut.congr e) g) ∈ H
  rwa [MulEquiv.symm_apply_apply]

private theorem pull_base (e : A ≃* B) {a b : B}
    (h : Subgroup.closure ({a,b} : Set B) = ⊤) :
    Subgroup.closure ({e.symm a, e.symm b} : Set A) = ⊤ := by
  have hh := congrArg (Subgroup.map e.symm.toMonoidHom) h
  rw [← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr e.symm.surjective] at hh
  simpa [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton] using hh

/-- Pull a Hall–Janko frame back through a change of coordinates. -/
public def HallJankoAutActions.of_map (e : A ≃* B) (H K : Subgroup (MulAut A))
    (s : HallJankoAutActions (H.map (MulAut.congr e).toMonoidHom)
      (K.map (MulAut.congr e).toMonoidHom)) : HallJankoAutActions H K where
  a := e.symm s.a
  b := e.symm s.b
  a_four := by rw [← map_pow, s.a_four, map_one]
  b_four := by rw [← map_pow, s.b_four, map_one]
  ba := by rw [← map_mul, s.ba, map_mul]
  base := pull_base e s.base
  four := by
    have hh := congrArg (Subgroup.map e.symm.toMonoidHom) s.four
    rw [e.symm.map_omega 2 1] at hh
    simpa [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      map_pow] using hh
  u := (MulAut.congr e).symm s.u
  v := (MulAut.congr e).symm s.v
  t := (MulAut.congr e).symm s.t
  u_mem := pull_mem e H s.u_mem
  v_mem := pull_mem e H s.v_mem
  t_mem := pull_mem e K s.t_mem
  ua := by rw [pull_apply, s.ua, map_mul, map_inv, map_pow]
  ub := by rw [pull_apply, s.ub, map_inv]
  va := by rw [pull_apply, s.va, map_mul, map_pow]
  vb := by rw [pull_apply, s.vb, map_mul, map_pow]
  ta := by rw [pull_apply, s.ta, map_mul]
  tb := by rw [pull_apply, s.tb, map_inv]

/-- Pull a split-inversion frame back through a change of coordinates. -/
public def SplitInversionAutActions.of_map (e : A ≃* B) (H K : Subgroup (MulAut A))
    (s : SplitInversionAutActions (H.map (MulAut.congr e).toMonoidHom)
      (K.map (MulAut.congr e).toMonoidHom)) : SplitInversionAutActions H K where
  a := e.symm s.a
  b := e.symm s.b
  a_four := by rw [← map_pow, s.a_four, map_one]
  b_four := by rw [← map_pow, s.b_four, map_one]
  ba := by rw [← map_mul, s.ba, map_mul]
  base := pull_base e s.base
  a_two_ne := by
    intro h
    apply s.a_two_ne
    apply e.symm.injective
    simpa only [map_pow, map_one] using h
  b_two_ne := by
    intro h
    apply s.b_two_ne
    apply e.symm.injective
    simpa only [map_pow, map_one] using h
  squares_ne := by
    intro h
    apply s.squares_ne
    apply e.symm.injective
    simpa only [map_pow] using h
  u := (MulAut.congr e).symm s.u
  v := (MulAut.congr e).symm s.v
  t := (MulAut.congr e).symm s.t
  u_mem := pull_mem e H s.u_mem
  v_mem := pull_mem e H s.v_mem
  t_mem := pull_mem e K s.t_mem
  ua := by rw [pull_apply, s.ua, map_inv]
  ub := by rw [pull_apply, s.ub]
  va := by rw [pull_apply, s.va]
  vb := by rw [pull_apply, s.vb, map_inv]
  ta_two := by rw [← map_pow, pull_apply, s.ta_two, map_pow]
  tb_two := by rw [← map_pow, pull_apply, s.tb_two, map_pow]
  tut := by rw [← map_inv, ← map_mul, ← map_mul, s.tut]
  tvt := by rw [← map_inv, ← map_mul, ← map_mul, s.tvt]

end C4SquareExtension
