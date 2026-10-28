module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ResidualLocal
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SmallResidualExclusion

/-!
# Large original amalgams and their universal two-perfect normal base

The original common Sylow order bound excludes the cubic and alternating local
residuals before passing to the universal tree. Exact local residual equivalences
then transfer those exclusions to the actual two-perfect normal base. No lower
order bound is asserted for its common Sylow. This is the input reduction for
Goldschmidt (1980), Sections 4–6, in the F.1.12 large marked branch.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

/-- The actual universal two-perfect normal base avoids both small local
residuals. The lower bound is used only on the original common Sylow. -/
theorem large_universal_residual_setup
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (hA : generalizedFitting A = pCore 2 A)
    (hB : generalizedFitting B = pCore 2 B)
    (hlarge : 64 ≤ Nat.card (A ⊓ B : Subgroup G)) :
    let F := residualFamily (RankTwoAmalgam.Universal.cosetFamily (inclusionAmalgam A B))
    TwoPerfectTreeAction F ∧
      (∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3))) ∧
      (∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4))) := by
  let F := residualFamily (RankTwoAmalgam.Universal.cosetFamily (inclusionAmalgam A B))
  have e (i : Bool) : pResidual 2 (F i) ≃* pResidual 2 (if i then B else A : Subgroup G) := by
    cases i
    · exact universalResidualLeftEquiv h hcore
    · exact universalResidualRightEquiv h hcore
  refine ⟨twoPerfectResidual_of_goldschmidt h hcore,?_,?_⟩
  · intro i hi
    obtain ⟨c⟩ := hi
    exact original_residual_not_cubic hA hB i ⟨(e i).symm.trans c⟩
  · intro i hi
    obtain ⟨a⟩ := hi
    exact original_residual_not_alternating h hcore hA hB hlarge i ⟨(e i).symm.trans a⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
