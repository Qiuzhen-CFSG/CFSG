module

public import Theory.GroupTheory.TwoPerfectCubicQuaternion
public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction

/-!
# Faithful cubic two-perfect groups in odd-characteristic GL₂

The determinant kills the two-core, since the actor is two-perfect and
the determinant image is abelian. Every core involution is therefore the
scalar -I. The unique-involution cubic extension theorem identifies the
actual actor with SL₂(3) and its actual two-core with Q₈.

Source: Aschbacher–Smith 13.3.14(d), printed p.892. The proof uses the
original faithful matrix action and includes arbitrary finite odd fields.
-/

public section
open Subgroup

namespace Matrix.GeneralLinearGroup

variable {A F : Type*} [Group A] [Finite A] [Field F] [Finite F]

theorem binaryTetrahedral_of_faithful_cubic_action
    (hF : (2 : F) ≠ 0) (hA : IsPPerfect 2 A)
    (hthree : Nat.card (A ⧸ pCore 2 A) = 3) (hne : pCore 2 A ≠ ⊥)
    (f : A →* GL (Fin 2) F) (hf : Function.Injective f) :
    Nonempty (A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
      Nonempty ((pCore 2 A) ≃* QuaternionGroup 2) := by
  have hd : pCore 2 A ≤ (det.comp f).ker :=
    (Subgroup.map_eq_bot_iff _).mp (hA.twoCore_map_eq_bot_of_commutative (det.comp f))
  have hscalar (x : pCore 2 A) (hx : orderOf x = 2) : f x = -1 := by
    have hs : f x ^ 2 = 1 := by
      have hh := congrArg (fun a : pCore 2 A => f a) (hx ▸ pow_orderOf_eq_one x)
      change f (x.val ^ 2) = f (1 : A) at hh
      rw [map_pow, map_one] at hh
      exact hh
    rcases eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one hF (f x) hs (hd x.property) with h | h
    · have he : x = 1 := Subtype.ext (hf (h.trans f.map_one.symm))
      simp only [he, orderOf_one] at hx
      omega
    · exact h
  exact binaryTetrahedral_of_cubic_quotient hA hthree hne
    (fun x y hx hy => Subtype.ext (hf ((hscalar x hx).trans (hscalar y hy).symm)))

end Matrix.GeneralLinearGroup
