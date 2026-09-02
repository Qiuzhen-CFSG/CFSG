import Stellmacher.FinalTheorem

namespace Stellmacher

set_option autoImplicit true

example
    {H : Type u} [Group H] [Finite H]
    (hN2 : IsNTwoGroup H) (hEven : Even (Nat.card H))
    (S0 : Sylow 2 H) :
    IsOfExceptionalType S0 ∨
    (IsDihedralGroup S0 ∨ IsSemidihedralGroup S0) ∨
    (Nat.card S0 = 2 ^ 5 ∧
      ∃ U : Subgroup H,
        Theory.Quasithin.IsMaximalTwoLocal U ∧
        Nonempty (U ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))) ∨
    (∃ M : Subgroup H, Theory.Comparator.IsStronglyEmbedded M) ∨
    (∃ U : Subgroup H,
      Theory.Quasithin.IsTwoLocal U ∧ pPrimeCore 2 U ≠ ⊥) := by
  exact?

#print axioms Stellmacher.theorem_two
#print axioms Stellmacher.theorem_one

end Stellmacher
