module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.QuotientTheta.SecondChoice.Extension

/-!
# Quotient calculations for the second choice in 15.3.10

The ordinary branch identifies Y₊S/O₂(Y₊S) with S₃ and its core with
C_S(V₂). The extraspecial branch identifies Y₊/O₂(Y₊) with E₉ and the
literal O₂ quotient of Y₊S with S₃×S₃, and proves R=C_T(V). It uses the
actual selected subgroup, natural image of S, and their compatible action.

`second_choice_quotient_and_core` splits the genuine earlier 15.3.7
alternatives and completes these second-choice quotient and core
calculations. The broader 15.3.11 assembly remains with the parent.
The earlier reduction is retained with its original public statement.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.7 and the second-choice proof of 15.3.11(5), printed pp.1122–1124.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches.QuotientTheta
open FusionCore.CosetSetup.ExtraspecialLocal
variable {G : Type*} [Group G] [Finite G]

/-- Split the earlier alternatives, with the selected quotients and both
core identities proved before the remaining extraspecial extension recognition. -/
theorem second_choice_quotient_reduction (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus) (hsecond : OutsideStructure.SecondChoice d)
    (h7 : EarlierThreeAlternatives d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hcore : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hSylow : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S) :
    (Nonempty ((↥(d.Yplus ⊔ d.S) ⧸ pCore 2 ↥(d.Yplus ⊔ d.S)) ≃*
        Equiv.Perm (Fin 3)) ∧ d.R = d.S ⊓ centralizer (d.V₂ : Set G)) ∨
      (ExtraspecialCase d.M d.Y d.V ∧
        Nonempty ((d.Yplus ⧸ pCore 2 d.Yplus) ≃* Multiplicative (Fin 2 → ZMod 3)) ∧
        d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) := by
  rcases h7 with hord | ⟨hextra, _⟩
  · exact Or.inl (second_choice_ordinary_quotient_and_core d I hI hsecond hord h7image hSylow)
  · exact Or.inr ⟨hextra, second_choice_extraspecial_selected_quotient d hsecond h7image hextra,
      second_choice_extraspecial_core d I hI hsecond hcore h7image hextra hSylow⟩

/-- The quotient and core alternatives for the second choice of 15.3.10,
using the genuine earlier 15.3.7 alternatives. The extraspecial branch
proves the stronger quotient by O₂ used in the printed proof of 15.3.11. -/
theorem second_choice_quotient_and_core (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus) (hsecond : OutsideStructure.SecondChoice d)
    (h7 : EarlierThreeAlternatives d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hcore : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hSylow : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S) :
    (Nonempty ((↥(d.Yplus ⊔ d.S) ⧸ pCore 2 ↥(d.Yplus ⊔ d.S)) ≃*
        Equiv.Perm (Fin 3)) ∧ d.R = d.S ⊓ centralizer (d.V₂ : Set G)) ∨
      (Nonempty ((d.Yplus ⧸ pCore 2 d.Yplus) ≃* Multiplicative (Fin 2 → ZMod 3)) ∧
        Nonempty ((↥(d.Yplus ⊔ d.S) ⧸ pCore 2 ↥(d.Yplus ⊔ d.S)) ≃*
          (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
        d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) := by
  rcases h7 with hord | ⟨hextra, _⟩
  · exact Or.inl (second_choice_ordinary_quotient_and_core d I hI hsecond hord h7image hSylow)
  · exact Or.inr (second_choice_extraspecial_quotient_and_core
      d I hI hsecond hcore h7image hextra hSylow)

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches.QuotientTheta
end
