module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.Transport
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.SecondAction
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.QuotientCoordinates
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Theory.GroupTheory.PPerfectHom

/-!
# The hypothetical centralizing branch and its two definite planes

If [V,Y_L] is trivial, two-perfectness of Y_L excludes the faithful case
of 15.3.7. The remaining order-27 quotient of Y differs from the actual
order-nine quotient of Y₊, forcing the second choice of 15.3.10. The proved
orthogonal coordinate calculation then supplies the two plane normalizer
bounds, fixation of V₁ by Y_C, and V₂ = [V₂,Y_C].

The inputs are the used earlier quotient and action clauses, including an
actual E₉ quotient equivalence. No exponent-three assertion about Y₊ or
order-three assertion about Y_C is used. The final fixed-space contradiction
is performed in `Contradiction`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.7,
15.3.10–12 and the centralizing branch in 15.3.23, printed pp.1122–1128.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension
open OutsideStructure OutsideStructure.LocalBranches
variable {G : Type*} [Group G] [Finite G] (d : LocalData G) (L : Subgroup G)

/-- The genuine earlier quotient clauses force choice (2) under centralization. -/
theorem secondChoice_of_centralizing
    (hYL : YL d L ≠ ⊥)
    (he9 : Nonempty ((d.Yplus ⧸ pCore 2 d.Yplus) ≃* ComponentIntersection.ElementaryNine))
    (h7 : d.Y ⊓ centralizer (d.V : Set G) ≤ d.Y.pCoreIn 2 ∨
      Nat.card (d.Y ⧸ pCore 2 d.Y) = 27)
    (hcomm : ⁅d.V, YL d L⁆ = ⊥) : SecondChoice d := by
  have hAY : YL d L ≤ d.Y :=
    ((ComponentIntersection.intersectionResidual_le _ _).trans inf_le_left).trans
      (choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice)
  have hAC : YL d L ≤ centralizer (d.V : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have h27 : Nat.card (d.Y ⧸ pCore 2 d.Y) = 27 := by
    rcases h7 with hkernel | h27
    · have hAcore : YL d L ≤ d.Y.pCoreIn 2 := (le_inf hAY hAC).trans hkernel
      have he := (ComponentIntersection.intersectionResidual_isPPerfect d.Yplus L).hom_eq_one_of_isPGroup
        (d.Y.isPGroup_pCoreIn 2) (inclusion hAcore)
      exfalso
      apply hYL
      apply le_bot_iff.mp
      intro a ha
      exact congrArg (fun f : YL d L →* d.Y.pCoreIn 2 => (f ⟨a, ha⟩ : G)) he
    · exact h27
  have hne : d.Yplus ≠ d.Y := by
    obtain ⟨e9⟩ := he9
    have h9 : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9 := by
      rw [Nat.card_congr e9.toEquiv]
      change Nat.card (Fin 2 → ZMod 3) = 9
      simp
    intro he
    rw [he, h27] at h9
    contradiction
  exact d.choice.resolve_left hne

/-- The source normalizer bounds and both YC plane actions are derived in the hypothetical branch. -/
theorem centralizing_plane_actions
    (hYL : YL d L ≠ ⊥)
    (he9 : Nonempty ((d.Yplus ⧸ pCore 2 d.Yplus) ≃* ComponentIntersection.ElementaryNine))
    (h7 : d.Y ⊓ centralizer (d.V : Set G) ≤ d.Y.pCoreIn 2 ∨
      Nat.card (d.Y ⧸ pCore 2 d.Y) = 27)
    (h7image : d.action.image d.Y = Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hgen : d.Yplus = YL d L ⊔ YC d L)
    (hcomm : ⁅d.V, YL d L⁆ = ⊥) :
    normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M ∧
      d.V₁ ≤ centralizer (YC d L : Set G) ∧ ⁅d.V₂, YC d L⁆ = d.V₂ := by
  have hs : SecondChoice d := secondChoice_of_centralizing d L hYL he9 h7 hcomm
  obtain ⟨hn1, hn2, _⟩ := second_choice_normalizers d hs h7image
  have hCY : YC d L ≤ d.Yplus := (ComponentIntersection.centralizerResidual_le _ _).trans inf_le_left
  have hplus : d.Yplus ≤ centralizer (d.V₁ : Set G) := by
    rw [hs.2]
    exact (map_subtype_le _).trans inf_le_right
  have hLC : YL d L ≤ centralizer (d.V₂ : Set G) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
      (centralizer_le (d.action.plane_le _))
  have hCN : YC d L ≤ normalizer (d.V₂ : Set G) :=
    hCY.trans ((choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice).trans
      (y_normalizes_plane d (Multiplicative.ofAdd (1 : ZMod 2))))
  have hVC : d.V₁ ≤ centralizer (YC d L : Set G) :=
    le_centralizer_iff.mp (hCY.trans hplus)
  have hcommC : ⁅d.V₂, YC d L⁆ = ⁅d.V₂, d.Yplus⁆ :=
    commutator_eq_of_centralizing_sup (V := d.V₂) (B := d.Yplus)
      (C := YL d L) (X := YC d L) hgen.symm hLC hCN
  have hmove : ⁅d.V₂, YC d L⁆ = d.V₂ :=
    hcommC.trans (second_choice_commutator d hs h7image).2
  exact ⟨hn1, hn2, hVC, hmove⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.Extension

end
