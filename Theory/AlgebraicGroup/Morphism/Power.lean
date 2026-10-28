module

public import Theory.AlgebraicGroup.Morphism.Basic
public import Theory.AlgebraicGroup.Morphism.Operations

universe u

/-! Natural-power maps on algebraic groups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The natural-power map on an algebraic group is a polynomial morphism of
varieties. It need not be a group morphism when the group is noncommutative. -/
@[expose]
public def npowMorphism
    (G : Variety k) [AlgebraicGroup G] : ℕ → Variety.Morphism G G
  | 0 => Variety.Morphism.const G G 1
  | n + 1 =>
      (mulMorphism G).comp
        ((npowMorphism G n).pair (Variety.Morphism.id G))

/-- The point map of `npowMorphism` is ordinary natural exponentiation. -/
public lemma npowMorphism_apply
    (G : Variety k) [AlgebraicGroup G] (n : ℕ) (x : Variety.Point G) :
    (npowMorphism G n).toFun x = x ^ n := by
  induction n with
  | zero =>
      simp [npowMorphism, Variety.Morphism.const]
  | succ n ih =>
      change (npowMorphism G n).toFun x * x = x ^ (n + 1)
      rw [ih, pow_succ]

/-- On an algebraic group with commutative point group, natural exponentiation
is an algebraic-group morphism. -/
@[expose]
public def commutativeNpowMorphism
    (G : Variety k) [AlgebraicGroup G]
    (hG : IsMulCommutative (Variety.Point G)) (n : ℕ) :
    AlgebraicGroup.Morphism G G where
  toVariety := npowMorphism G n
  map_one := by
    rw [npowMorphism_apply, one_pow]
  map_mul := by
    intro x y
    rw [npowMorphism_apply, npowMorphism_apply, npowMorphism_apply]
    exact (show Commute x y from (isMulCommutative_iff.mp hG) x y).mul_pow n

end Theory.AlgebraicGroup
