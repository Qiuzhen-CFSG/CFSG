module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCoreRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.ReducedSolvability

/-!
# Solvability filters for the original A5 pair

Every overgroup of either original A5-marked factor is nonsolvable. This
excludes binary core quotients separately at the original local, reduced
join and full reduced parabolic levels. Each exceptional catalogue model
has a solvable right endpoint, so its weaker parabolic comparison is
excluded in either orientation. No exceptional comparison is upgraded to
an isomorphism of inclusion diagrams.

Source: Aschbacher–Smith F.1.12(I)(8–13), pp.262–264; DGS Theorem A and
(15.3), pp.99–100 and 229–231.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.A5PairCatalogue
open SuzukiContainment DGS85.OriginalExtension
open Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}

omit [Finite G] in
/-- Any overgroup of an original A5-marked factor is nonsolvable. -/
theorem overgroup_not_solvable (i : Fin 2)
    (a : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))
    {P : Subgroup G} (hP : L i ≤ P) : ¬ Group.IsSolvable P := by
  intro hs
  let := hs
  let : Group.IsSolvable (L i) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hP)
  let : Group.IsSolvable (alternatingGroup (Fin 5)) :=
    Group.isSolvable_of_surjective (f := a.toMonoidHom) a.surjective
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance

/-- Excludes binary quotients at the local, joined and full-parabolic levels,
without identifying any of these three quotients with another. -/
theorem not_binary_overgroup_quotient (i : Fin 2)
    (a : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))
    {P : Subgroup G} (hP : L i ≤ P) :
    ¬ ClassicalGroup.IsPSL (P ⧸ pCore 2 P) 2 2 := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  let := Theory.PSL2.OuterSolvable.isSolvable_of_card_two hF
  let : Group.IsNilpotent (pCore 2 P) := pCore_isNilpotent
  exact overgroup_not_solvable i a hP
    ((Group.isSolvable_iff_subgroup_quotient (pCore 2 P)).mpr
      ⟨inferInstance, Group.isSolvable_of_isSolvable_injective
        (f := e.toMonoidHom) e.injective⟩)

omit [Finite G] in
/-- All eight exceptional rows are excluded at their genuine weaker
parabolic comparison, with either original orientation. -/
theorem not_reduced_exceptional
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    (c : GreenBook.ExceptionalModels.Case) :
    ¬ (GreenBook.ExceptionalModels.ParabolicModel c (reducedAmalgam L S) ∨
      GreenBook.ExceptionalModels.ParabolicModel c (reducedAmalgam L S).reverse) := by
  rintro (he | he)
  · exact overgroup_not_solvable 1 (a 1).some (le_sup_left.trans le_sup_left)
      (ExceptionalComparison.right_solvable c _ he)
  · exact overgroup_not_solvable 0 (a 0).some (le_sup_left.trans le_sup_left)
      (ExceptionalComparison.right_solvable c _ he)

end CFSG.Quasithin.ChapterF.Source.A5PairCatalogue
