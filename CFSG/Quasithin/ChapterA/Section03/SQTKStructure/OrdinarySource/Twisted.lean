module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Basic
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers
/-!
# Twisted ordinary components in A.3.6

The actual triality odd-prime covering calculation makes the center a
two-group. Trivial two-core therefore recovers the original simple model.
Every branch supplies the full common Fitting and radical conclusion.

Source: Aschbacher–Smith A.3.6 and I.1.3, printed pp.43–45, 407.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.SQTKStructure.OrdinarySource
open Chapter1.Section02 Chapter1.Section02.LocalModels

/-- Every triality ordinary component, including the smallest parameter,
has trivial center by the actual odd-prime cover calculation. -/
theorem a36_triality {X : Type*} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (n : ℕ) (hn : 1 ≤ n)
    (hmodel : Triality.Standard.IsTrialityGroupAt (2 ^ n) (L ⧸ center L)) :
    A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  have hz : center L = ⊥ := by
    apply bot_unique
    rw [← hcore]
    exact le_sSup ⟨inferInstance,
      Triality.InnerDisplacement.PrimeToTwoCovers.center_isTwoGroup n (by omega) hmodel⟩
  let j : L ≃* L ⧸ center L :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hz.symm)
  let : IsSimpleGroup L := j.isSimpleGroup
  exact simple_conclusion L hL (.rank_two (.triality n hn (hmodel.of_mulEquiv j)))
end CFSG.Quasithin.ChapterA.SQTKStructure.OrdinarySource
