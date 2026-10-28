module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.Statements
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalControl
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.Geometry
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.SecondAction
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.QuotientTheta.Generation
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.QuotientTheta.Cores
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.QuotientTheta.FirstChoice
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.QuotientTheta.SecondChoice

/-!
# Theta and algebraic calculations for the outside local branches

`chosen_eq_theta` proves Y₊=theta(M∩I) for both choices from the full earlier
15.3.7 alternatives and the independently established residual-intersection
identity. In the ordinary alternative, `ordinary_chosen_primeToResidual`
also proves the literal O^{3′}(M∩I) identity. The core calculation identifies
O₂(YS)=C_T(V) and places this subgroup in O₂(Y₊S) in either choice.

`algebraic_alternative` combines the actual quotient calculations with
these core and residual identities. The first choice always gives the
rank-two algebraic clauses. In the second choice the ordinary earlier
alternative gives the complete RankOneCase, while the extraspecial earlier
alternative gives the rank-two clauses. In the latter case the trivial
Frattini subgroup of S₃ × S₃ converts the proved two-core quotient to the
literal Frattini-preimage quotient.

`quotient_and_theta` supplies both outputs to the local-branch assembly.
The Sylow witness and second-choice residual-intersection identity remain
explicit, independently established inputs; no current quotient or local
structural alternative is assumed. The remaining rank-two normality,
radical, Sylow-span and normalizer-control clauses belong to the assembly
in OutsideStructure.LocalBranches.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.7 and 15.3.11(5)–(6), printed pp.1122–1124.
-/

public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches.QuotientTheta
variable {G : Type*} [Group G] [Finite G]

/-- The algebraic clauses of (5i), or all of (5ii), from the genuine earlier
15.3.7 alternatives and the independently established clauses (1) and (3). -/
theorem algebraic_alternative (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus) (h7 : EarlierThreeAlternatives d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h7core : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hSylow : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S)
    (hintersection : SecondChoice d → d.Yplus = twoResidualAmbient (d.Y ⊓ I)) :
    (CubicQuotient (d.Yplus ⧸ pCore 2 d.Yplus) ∧
      Nonempty ((↥(d.Yplus ⊔ d.S) ⧸ coreFrattiniSubgroup ↥(d.Yplus ⊔ d.S)) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      d.R = (d.Y ⊔ d.S).pCoreIn 2 ∧
      d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) ∨ RankOneCase d I := by
  rcases d.choice with hfirst | hsecond
  · exact Or.inl ⟨first_choice_cubic_quotient d hfirst h7,
      first_choice_frattini_quotient d hfirst h7 h7image h7core,
      first_choice_core d hfirst h7core⟩
  · rcases h7 with hord | ⟨hextra, _⟩
    · obtain ⟨hquotient, hR⟩ :=
        second_choice_ordinary_quotient_and_core d I hI hsecond hord h7image hSylow
      exact Or.inr ⟨hsecond, hquotient,
        ordinary_chosen_primeToResidual d I hI hord hintersection, hR⟩
    · obtain ⟨hselected, hquotient, hR⟩ :=
        second_choice_extraspecial_quotient_and_core d I hI hsecond h7core h7image hextra hSylow
      exact Or.inl ⟨Or.inl hselected, coreFrattini_quotient_of_twoCore hquotient,
        hR.trans (ys_core_eq_centralizer d h7core).symm, hR⟩

/-- The quotient/core calculation and theta identity needed by the final
15.3.11 local-branch assembly, with no additional recognition premises. -/
theorem quotient_and_theta (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus) (h7 : EarlierThreeAlternatives d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h7core : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hSylow : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S)
    (hintersection : SecondChoice d → d.Yplus = twoResidualAmbient (d.Y ⊓ I)) :
    d.Yplus = theta (d.MI I) ∧
      ((CubicQuotient (d.Yplus ⧸ pCore 2 d.Yplus) ∧
        Nonempty ((↥(d.Yplus ⊔ d.S) ⧸ coreFrattiniSubgroup ↥(d.Yplus ⊔ d.S)) ≃*
          (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
        d.R = (d.Y ⊔ d.S).pCoreIn 2 ∧
        d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) ∨ RankOneCase d I) :=
  ⟨chosen_eq_theta d I hI h7 hintersection,
    algebraic_alternative d I hI h7 h7image h7core hSylow hintersection⟩

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches.QuotientTheta

end
