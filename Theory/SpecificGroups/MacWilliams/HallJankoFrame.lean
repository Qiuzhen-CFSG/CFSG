module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Fin.VecNotation

/-!
# Action frames for Hall–Janko extensions

A frame records a marked C₄-square base, two commuting involutions in an
elementary sixteen, and one further lift. Its conjugation actions describe
an order-eight quotient of the base. The square of the further lift and its
products with the two inner involutions are deliberately separate conditions.

Once those three conditions hold, the tuple `(t,u,v,b,u*a,a²,b²)` satisfies
the Hall–Janko table; `HallJankoExtension` proves that calculation and generation.
Existence and normalization of a frame remain structural proof obligations.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3(a), printed p.386,
citing MacWilliams, Trans. AMS 150 (1970), DOI 10.1090/S0002-9947-1970-0276324-3.
The coordinate choice was discovered with GAP SmallGroup(128,934); the
conversion to the presentation is proved in Lean without a GAP oracle.
-/

@[expose] public section

namespace MacWilliamsSylow

/-- A marked abelian base and the specified conjugation actions, before normalizing lifts. -/
structure HallJankoActionFrame {P : Type*} [Group P] (D W B : Subgroup P) where
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
  u_two : u * u = 1
  v_two : v * v = 1
  vu : v * u = u * v
  ua : u * a = a⁻¹ * b ^ 2 * u
  ub : u * b = b⁻¹ * u
  va : v * a = a * b ^ 2 * v
  vb : v * b = a ^ 2 * b * v
  ta : t * a = a * b * t
  tb : t * b = b⁻¹ * t
  generate : Subgroup.closure ({a, b, u, v, t} : Set P) = ⊤

namespace HallJankoActionFrame
/-- The three lift equations needed in addition to the action on the base. -/
structure LiftRelations {P : Type*} [Group P] {D W B : Subgroup P}
    (f : HallJankoActionFrame D W B) : Prop where
  t_two : f.t * f.t = 1
  tu : f.t * f.u = f.b⁻¹ * f.u * f.t
  tv : f.t * f.v = f.a⁻¹ * f.u * f.v * f.t

/-- The seven generators in the zero-based order used by `hallJankoTable`. -/
def tuple {P : Type*} [Group P] {D W B : Subgroup P}
    (f : HallJankoActionFrame D W B) : Fin 7 → P :=
  ![f.t, f.u, f.v, f.b, f.u * f.a, f.a ^ 2, f.b ^ 2]

end HallJankoActionFrame
end MacWilliamsSylow
