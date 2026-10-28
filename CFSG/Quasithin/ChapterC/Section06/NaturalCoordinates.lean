module
public import CFSG.Quasithin.ChapterC.Section06.RankOneSource
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Solvable
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# Internal coordinates for the original natural block

The C.5 marking of a specified L₂(2ⁿ) block retains its internal Sylow action.
Its alternative A₃ marking would make the original block isomorphic to A₄
and solvable, contradicting the perfect higher-field quotient.

Source: Aschbacher--Smith C.5.4 and 2.4.8, printed pp.155,529--530.
-/

public section
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] {R K : Subgroup G} {F : Type*} [Field F]

theorem Setup.internal_of_linear (h : Setup R K F) {n : ℕ} (hK : IsL2EvenBlock K n) :
    h.coordinates.IsInternal := by
  rcases h.block with ⟨_,_,hi⟩ | ha
  · exact hi
  · obtain ⟨e⟩ := ha.equiv_alternatingFour
    let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup_fin_four_isSolvable
    let : Group.IsSolvable K :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact hK.not_solvable.elim

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
