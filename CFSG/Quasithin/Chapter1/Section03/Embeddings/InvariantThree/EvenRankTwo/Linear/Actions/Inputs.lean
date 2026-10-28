module

public import Theory.SpecificGroups.PSL3.CartanActions

/-!
# Model inputs for the ternary PSL₃ Borel action

The two remaining independent calculations are expressed here without any
power-orbit or reducibility conclusion. StandardCompatibility consists of
three matrix identities for the actual projective actions. BorelThreeAlignment
asks for simultaneous conjugation of a Sylow two-subgroup and a normalizing
commutative three-subgroup to the specified unipotent subgroup and diagonal torus.

Their source assembly is in Actions. Source: Aschbacher–Smith, Proposition
1.3.4, printed p.511 (PDF p.528 of `refs/quasithin.pdf`).
-/

@[expose] public section

open scoped MatrixGroups
open Subgroup Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Matrix.PSL3.OuterSolvable
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Actions
variable (F : Type*) [Field F]

/-- The three genuine matrix laws needed by the standard-element normal form. -/
def StandardCompatibility : Prop :=
  (∀ (σ : F ≃+* F) (m : GL (Fin 3) F),
    fieldAction F σ * linearConj F m =
      linearConj F (Matrix.GeneralLinearGroup.map σ.toRingHom m) * fieldAction F σ) ∧
  (∀ m : GL (Fin 3) F, ∃ m' : GL (Fin 3) F,
    graph F * linearConj F m = linearConj F m' * graph F) ∧
  (∀ σ : F ≃+* F, Commute (fieldAction F σ) (graph F))

/-- Simultaneous alignment of the actual Sylow subgroup and its normalizing
commutative three-subgroup. This geometric input contains no action conclusion. -/
def BorelThreeAlignment : Prop :=
  ∀ (f : ℕ), 2 ≤ f → Nat.card F = 2 ^ f →
    ∀ (S : Sylow 2 PSL(3,F)) (B : Subgroup PSL(3,F)),
      IsPGroup 3 B → IsMulCommutative B → B ≤ normalizer (S : Subgroup PSL(3,F)) →
      ∃ a : MulAut PSL(3,F),
        (S : Subgroup PSL(3,F)).map a.toMonoidHom = unipotent F ∧
          B.map a.toMonoidHom ≤ torus F

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Actions
