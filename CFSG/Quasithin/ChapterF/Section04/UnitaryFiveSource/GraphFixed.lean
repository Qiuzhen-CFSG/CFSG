module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.GraphFixed
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.Model

/-!
# Projective graph-fixed subgroup in the actual U₅(4) model

Specialize the scalar-corrected graph descent to the stored field, Hermitian
form and projective carrier of `Model 4`. The resulting equivalence uses the
actual order-five kernel in SU₅(4) → PSU₅(4); it does not replace PSU by SU.
This is the graph-fixed projective carrier needed before identifying it with
the fixed-field Sp₄(4) group in F.4.37.

Source: Aschbacher--Smith F.4.37(1), printed p.293 of `refs/quasithin.pdf`.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model

/-- The actual projective U₅(4) graph-fixed subgroup is the image of the
actual SU₅(4) graph-fixed subgroup under the same projective map. -/
noncomputable def graph_fixed_projective_equiv (U : Model 4) :
    (Theory.SpecificGroups.UnitaryFive.GraphFixed.matrixAut U.form U.matrix).fixedSubgroup ≃*
      (Theory.SpecificGroups.UnitaryFive.GraphFixed.projectiveAut U.form U.matrix).fixedSubgroup := by
  have hF : Nat.card U.F = 16 := by simpa using U.card
  exact Theory.SpecificGroups.UnitaryFive.GraphFixed.fixedProjectEquiv
    U.form U.matrix U.conjugation hF

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
