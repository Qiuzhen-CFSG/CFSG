module

public import Theory.SpecificGroups.MacWilliams.HallJankoFrame
public import Theory.ElementaryAbelian.Basic

/-!
# The base actions before proving generation

This interface separates selecting a basis and conjugation lifts from proving
that those lifts generate the whole extension. In an elementary subgroup,
the two selected lifts are automatically commuting involutions. Supplying
generation therefore gives precisely the existing Hall–Janko action frame.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3(a), printed p.386,
citing MacWilliams, Trans. AMS 150 (1970), DOI 10.1090/S0002-9947-1970-0276324-3.
-/

@[expose] public section
namespace MacWilliamsSylow

/-- A marked C₄-square and the six base actions, without a generation premise. -/
structure HallJankoBaseActions {P : Type*} [Group P] (D W B : Subgroup P) where
  a : P
  b : P
  u : P
  v : P
  t : P
  a_four : a ^ 4 = 1
  b_four : b ^ 4 = 1
  ba : b * a = a * b
  base : D = Subgroup.closure ({a, b} : Set P)
  four : W = Subgroup.closure ({a ^ 2, b ^ 2} : Set P)
  u_mem : u ∈ B
  v_mem : v ∈ B
  ua : u * a = a⁻¹ * b ^ 2 * u
  ub : u * b = b⁻¹ * u
  va : v * a = a * b ^ 2 * v
  vb : v * b = a ^ 2 * b * v
  ta : t * a = a * b * t
  tb : t * b = b⁻¹ * t

namespace HallJankoBaseActions

/-- Generation upgrades the base actions to the full action frame. -/
def toFrame {P : Type*} [Group P] {D W B : Subgroup P}
    [IsElementaryAbelian 2 B] (f : HallJankoBaseActions D W B)
    (hgen : Subgroup.closure ({f.a, f.b, f.u, f.v, f.t} : Set P) = ⊤) :
    HallJankoActionFrame D W B where
  a := f.a
  b := f.b
  u := f.u
  v := f.v
  t := f.t
  a_four := f.a_four
  b_four := f.b_four
  ba := f.ba
  base := f.base
  four := f.four
  u_mem := f.u_mem
  v_mem := f.v_mem
  u_two := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) f.u f.u_mem
  v_two := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) f.v f.v_mem
  vu := congrArg (fun x : B => (x : P))
    (IsMulCommutative.is_comm.comm (⟨f.v, f.v_mem⟩ : B) ⟨f.u, f.u_mem⟩)
  ua := f.ua
  ub := f.ub
  va := f.va
  vb := f.vb
  ta := f.ta
  tb := f.tb
  generate := hgen

end HallJankoBaseActions
end MacWilliamsSylow
