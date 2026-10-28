module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.Exhaustion.Structure
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable

/-!
# Quotients by recognized simple cores

Conjugation embeds the actual quotient `U/N` into `Aut(N)/Inn(N)` when
`N` is normal in `U` and has trivial centralizer there. The imported
`SolvableOuterQuotient` development constructs this map and proves its
injectivity, without any splitting assumption.

The A₆ branch is proved using its outer quotient of order four. The remaining
three model calculations are explicit inputs to the assembly below: PSL₂(q),
PSL₃(2^m), and PSU₃(2^m). The separately listed PSL₃(2) core uses `m = 1`.
These are genuine model automorphism questions, not conclusions supplied by
`CoreModel`. Until these inputs are proved, the full quotient contract remains
unconditional work to be completed by this module's owner.

Source: GLS3, Theorem 6.5.3 and its final extension-control argument,
`refs/KGroup/GLS3/chapter6.tex`. The source gives more precise inner-diagonal
control; only quotient solvability is needed for the subgroup envelope here.
No K-group hypothesis or section classification is used.
-/

namespace CFSG.Quasithin.MainConverse.LinearThreeSections

open Matrix
open scoped MatrixGroups

/-- The A₆ core branch has solvable quotient, with normality and centralizer
computed in the actual overgroup. -/
public theorem alternatingSix_core_quotient_isSolvable
    {H : Type} [Group H] (N : Subgroup H) [N.Normal]
    (hc : Subgroup.centralizer (N : Set H) = ⊥)
    (e : N ≃* alternatingGroup (Fin 6)) : Group.IsSolvable (H ⧸ N) := by
  let : Group.IsSolvable (MulAut.Outer (alternatingGroup (Fin 6))) :=
    AlternatingSix.ShadowLocal.outer_isSolvable
  let : Group.IsSolvable (MulAut.Outer N) := MulAut.isSolvable_outer_of_mulEquiv e
  exact N.quotient_isSolvable_of_centralizer_eq_bot hc

/-- Conditional assembly of the exact quotient contract in
`proper_subgroup_envelope_of_core_inputs`. Only the three named model outer
quotient calculations remain as extra inputs; A₆ is discharged here. -/
public theorem recognized_core_quotient_isSolvable_of_model_outer_inputs
    (hlinearTwo : ∀ (S : Type) [Group S] [IsSimpleGroup S],
      ¬ Group.IsSolvable S → ∀ q, ClassicalGroup.IsPSL S 2 q →
        Group.IsSolvable (MulAut.Outer S))
    (hlinearThree : ∀ (S : Type) [Group S] [IsSimpleGroup S],
      ¬ Group.IsSolvable S → ∀ m, 0 < m → ClassicalGroup.IsPSL S 3 (2 ^ m) →
        Group.IsSolvable (MulAut.Outer S))
    (hunitaryThree : ∀ (S : Type) [Group S] [IsSimpleGroup S],
      ¬ Group.IsSolvable S → ∀ m, 0 < m → ClassicalGroup.IsPSU S 3 (2 ^ m) →
        Group.IsSolvable (MulAut.Outer S))
    (f : ℕ) (_hf : 2 ≤ f) (F : Type) [Field F] [Finite F]
    (_hF : Nat.card F = 2 ^ f) (U : Subgroup PSL(3,F)) (_hU : U ≠ ⊤)
    (N : Subgroup U) [N.Normal] [IsSimpleGroup N]
    (hns : ¬ Group.IsSolvable N)
    (hc : Subgroup.centralizer (N : Set U) = ⊥) (hmodel : CoreModel N) :
    Group.IsSolvable (U ⧸ N) := by
  have : Group.IsSolvable (MulAut.Outer N) := by
    cases hmodel with
    | linearTwo q h => exact hlinearTwo N hns q h
    | binaryThree h => exact hlinearThree N hns 1 (by decide) (by simpa using h)
    | alternatingSix e =>
        obtain ⟨e⟩ := e
        let : Group.IsSolvable (MulAut.Outer (alternatingGroup (Fin 6))) :=
          AlternatingSix.ShadowLocal.outer_isSolvable
        exact MulAut.isSolvable_outer_of_mulEquiv e
    | linear m hm h => exact hlinearThree N hns m hm h
    | unitary m hm h => exact hunitaryThree N hns m hm h
  exact N.quotient_isSolvable_of_centralizer_eq_bot hc

end CFSG.Quasithin.MainConverse.LinearThreeSections
