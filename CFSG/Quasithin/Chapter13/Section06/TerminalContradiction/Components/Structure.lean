module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.Definitions
public import Theory.GroupTheory.CComponent.UniqueResidual
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterTwoGroup
public import Theory.Mathieu.M23.Properties.OuterRestriction
public import Theory.SpecificGroups.PSL3.OuterSolvable
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient

/-!
# From component isolation to the terminal structure

The three actual models have solvable outer automorphism groups; for J₂ and
M₂₃ they are two-groups. Combined with uniqueness of the C-component and
the prime-core exclusions, this proves the generalized-Fitting identity and
identifies the component with the solvable residual. For the sporadic models
it also proves the source generation equality with an actual Sylow subgroup.

The uniqueness and prime-core assertions remain explicit proof obligations.
In particular they must be established by the Suzuki/Borel argument and the
specialized A.3.18 application before these deductions complete 13.6.27.

The printed p.934 assertion O_{2,3}(G₁) = 1 is a typographical error: its
two-core contains the nonidentity central involution z. The needed corrected
assertion is O₃(G₁/O₂(G₁)) = 1, equivalently O_{2,3}(G₁) = O₂(G₁).
Together with 13.6.26(2), it gives F(G₁/O₂(G₁)) = 1, which is the input
used below. F and F* are kept distinct throughout.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma 13.6.27
and the following paragraph, printed pp.934–935.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components

open Subgroup Theory.GroupTheory

/-- The full outer group of the actual PSL₃(4) is solvable. -/
theorem l3Four_outer_isSolvable : Group.IsSolvable (MulAut.Outer L3Four) := by
  have hc : Nat.card F4 = 2 ^ 2 := GaloisField.card 2 2 (by decide)
  exact Matrix.PSL3.OuterSolvable.outer_isSolvable_of_standard_inputs F4
    (Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card F4 (by decide) hc)
    (Matrix.PSL3.OuterSolvable.standardOuter_isSolvable F4)

variable {H : Type*} [Group H] {T K : Subgroup H}

/-- Actual model equivalences supply outer solvability in all three cases. -/
theorem Candidate.outer_isSolvable (h : Candidate T K) :
    Group.IsSolvable (MulAut.Outer (K ⧸ pCore 2 K)) := by
  rcases h with h | h | ⟨e, _⟩
  · let _ := Sporadic.LeechRelated.J2.outer_isTwoGroup.isNilpotent
    exact MulAut.isSolvable_outer_of_mulEquiv (Classical.choice h)
  · let _ := Sporadic.Mathieu.m23_outer_isTwoGroup.isNilpotent
    exact MulAut.isSolvable_outer_of_mulEquiv (Classical.choice h)
  · let _ := l3Four_outer_isSolvable
    exact MulAut.isSolvable_outer_of_mulEquiv e

variable [Finite H]

/-- The genuine generalized-Fitting identity and the identification K = H∞,
after the remaining-component and prime-core exclusions have been proved. -/
theorem structure_of_unique_component (hK : K.IsCComponent)
    (hmodel : Candidate T K)
    (hunique : ∀ D : Subgroup H, D.IsCComponent → D = K)
    (hthree : pCore 3 (H ⧸ pCore 2 H) = ⊥)
    (hlarge : ∀ p : ℕ, p.Prime → 3 < p → pCore p (H ⧸ pCore 2 H) = ⊥) :
    generalizedFitting (H ⧸ pCore 2 H) = componentImage K ∧
      solvableResidual H = K := by
  have hf := fitting_twoCore_quotient_eq_bot hthree hlarge
  let _ := hmodel.outer_isSolvable
  exact ⟨hK.generalizedFitting_twoCore_quotient_eq hunique hf,
    hK.solvableResidual_eq_of_twoCore_quotient hunique hf⟩

/-- The complete generation conclusion in the J₂ and M₂₃ branches. -/
theorem sporadic_alternative_of_unique_component (S : Sylow 2 H)
    (hK : K.IsCComponent)
    (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23))
    (hunique : ∀ D : Subgroup H, D.IsCComponent → D = K)
    (hf : fittingSubgroup (H ⧸ pCore 2 H) = ⊥) :
    Alternative (S : Subgroup H) K := by
  have ho : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K)) := by
    rcases hmodel with h | h
    · exact Sporadic.LeechRelated.J2.outer_isTwoGroup.of_equiv
        (MulAut.outerCongr (Classical.choice h)).symm
    · exact Sporadic.Mathieu.m23_outer_isTwoGroup.of_equiv
        (MulAut.outerCongr (Classical.choice h)).symm
  exact Or.inl ⟨hK.sylow_sup_eq_top_of_outer_twoGroup hunique hf ho S, hmodel⟩

/-- The actual quotient equivalence after the terminal paragraph resets K := H∞.
Its target is the generalized Fitting subgroup, not the ordinary Fitting subgroup. -/
noncomputable def residualQuotientEquivGeneralizedFitting
    (hK : K.IsCComponent) (hmodel : Candidate T K)
    (hunique : ∀ D : Subgroup H, D.IsCComponent → D = K)
    (hthree : pCore 3 (H ⧸ pCore 2 H) = ⊥)
    (hlarge : ∀ p : ℕ, p.Prime → 3 < p → pCore p (H ⧸ pCore 2 H) = ⊥) :
    ((solvableResidual H) ⧸ pCore 2 (solvableResidual H)) ≃*
      generalizedFitting (H ⧸ pCore 2 H) := by
  obtain ⟨hf, hr⟩ := structure_of_unique_component hK hmodel hunique hthree hlarge
  let e := MulEquiv.subgroupCongr hr
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    ((cComponentTwoCoreQuotientEquiv hK).trans (MulEquiv.subgroupCongr hf.symm))

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components
