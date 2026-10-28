module

public import CFSG.Quasithin.ChapterC.Section01.BlockDefs
public import Theory.SpecificGroups.SL2.EvenBorelResidual
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.Solvable

/-!
# Numerical prerequisites for the binary linear Borel exclusion

The source exclusion of A₃-blocks in E.6.8 separates into two independent
calculations. A solvable short group with abelian two-core has order twelve.
A subnormal subgroup of a finite power of the actual PSL₂ Borel cannot have
that order when the field has order at least eight. The second assertion
retains subnormality in the whole power; arbitrary A₄ subgroups can occur.

These contracts separate the two calculations: `ShortOrder` and `BorelOrder`
prove their respective inputs. `LinearIntrinsic` supplies both to its core,
solvability and transport reductions, completing the intrinsic exclusion.
The finite matrix carriers have universe zero, so this boundary suffices even
when the original ambient group has an arbitrary universe.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7–13,
printed pp.123–125, and E.6.8, printed pp.247–248 (PDF pp.258–259).
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne

/-- The solvable short-group calculation needed after proving the actual
Borel power's subnormal two-core abelian. -/
def LinearShortOrderInput : Prop :=
  ∀ (A : Type) [Group A] [Finite A] [Group.IsSolvable A]
    [IsMulCommutative (pCore 2 A)], ChapterC.IsShort A → Nat.card A = 12

/-- The matrix Frobenius calculation, independently of short-group theory. -/
def LinearBorelOrderInput : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2]
    (n : ℕ), 3 ≤ n → Nat.card F = 2 ^ n →
      ∀ (k : ℕ) (X : Subgroup
        (Fin k → Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F)),
        X.IsSubnormal → Nat.card X ≠ 12

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne
