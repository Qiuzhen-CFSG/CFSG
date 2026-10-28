module

public import CFSG.Quasithin.ChapterA.Section01.RankActions.Inputs

/-!
# The linear recognition input to A.1.29

This is the remaining Dickson consequence needed by the actual-action
reduction. It requires genuine special-linear isomorphisms, including the
lift of the exceptional projective A₅ subgroup. No action, centralizer or
quasisimple-cover hypothesis occurs in this independent linear statement.
This module defines the contract; it does not prove it.

Source: Aschbacher–Smith, A.1.29(1), printed p.27, using corrected A.1.3.
-/

namespace CFSG.Quasithin.ChapterA.RankActions

/-- Nontrivial perfect subgroups of prime-field SL₂ are the whole group or
an exceptional SL₂(5), with its necessary prime congruence. -/
@[expose] public def PrimePerfectSL2Recognition : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p →
    ∀ K : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)),
      Group.IsPerfect K → Nontrivial K →
        Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) ∨
          ((p % 5 = 1 ∨ p % 5 = 4) ∧
            Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)))

end CFSG.Quasithin.ChapterA.RankActions
