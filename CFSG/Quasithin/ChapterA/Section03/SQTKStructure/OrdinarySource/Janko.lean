module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Basic
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.Janko

/-!
# The J₄ ordinary-component case of A.3.6

The actual odd-primary covering bound makes the center of the component
a two-group. Its trivial two-core therefore kills the center, and the
given quotient marking identifies the component itself with J₄.

Source: Aschbacher–Smith A.3.6 and I.1.3, printed pp.43–45, 407.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.SQTKStructure.OrdinarySource
open Chapter1.Section02

/-- The complete J₄ branch, with its odd-primary source input discharged. -/
theorem a36_janko_four {X : Type*} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (e : L ⧸ center L ≃* Janko4.Model) : A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  have hz : center L = ⊥ := by
    apply bot_unique
    rw [← hcore]
    exact le_sSup ⟨inferInstance, Janko4.OddPrimary.source_center_isPGroup ⟨e⟩⟩
  let j : L ≃* Janko4.Model := QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans e)
  let : IsSimpleGroup Janko4.Model := e.symm.isSimpleGroup
  let : IsSimpleGroup L := j.isSimpleGroup
  exact simple_conclusion L hL (.sporadic .j4 (by intro h; cases h) ⟨j⟩)

end CFSG.Quasithin.ChapterA.SQTKStructure.OrdinarySource
