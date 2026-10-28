module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.IntrinsicAction.CoreReduction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.IntrinsicAction.QuotientClassification

/-!
# Assembly of the intrinsic marked SL₃(4) alternatives

The marked action on the full Borel quotient distinguishes graph from
graph-field and puts the corresponding marked factor in the center times
the specified Sylow. Two-perfectness removes that Sylow part, giving an
equality of actual marked subgroups and the required embedded two-residual
comparison. The graph case uses the full cyclic action commutator; the
graph-field case uses the two-residual of the Borel fixed subgroup.

`alternatives` establishes both branches from the marked Borel hypotheses
and standard-automorphism coverage alone. It requires neither an invariant
chosen torus nor an involutory actor. Constructing the source marking and
discharging standard-automorphism coverage remain with the source assembly.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.955 (PDF p.972),
combined manuscript of 1 March 2004.
-/

public section
open Subgroup Representation.SL3FourNaturalDual
open Matrix.PSL3.OuterSolvable
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.IntrinsicAction

/-- Removing the two-part from the central quotient line completes both
source comparisons. `central_mod_sylow_alternatives` supplies this
disjunction from standard-automorphism coverage. -/
theorem of_central_mod_sylow_alternatives {α : MulAut SL} (d : MarkedBorelFactors α)
    (h :
      (∃ c : Matrix.GeneralLinearGroup (Fin 3) F,
        centerAction F α = linearConj F c * graph F ∧
          d.plusFactor ≤ center SL ⊔ (d.sylow : Subgroup SL)) ∨
      (∃ (c : Matrix.GeneralLinearGroup (Fin 3) F) (σ : F ≃+* F),
        σ ≠ 1 ∧ centerAction F α = linearConj F c * fieldAction F σ * graph F ∧
          d.zeroFactor ≤ center SL ⊔ (d.sylow : Subgroup SL))) :
    (∃ c : Matrix.GeneralLinearGroup (Fin 3) F,
      centerAction F α = linearConj F c * graph F ∧ d.plusFactor = center SL ∧
        let C := commutatorSubgroup (zpowers α) SL (normalizer (d.sylow : Set SL))
        (pResidual 2 C).map C.subtype = center SL) ∨
    (∃ (c : Matrix.GeneralLinearGroup (Fin 3) F) (σ : F ≃+* F),
      σ ≠ 1 ∧ centerAction F α = linearConj F c * fieldAction F σ * graph F ∧
        d.zeroFactor = center SL ∧
        let C := normalizer (d.sylow : Set SL) ⊓ α.fixedSubgroup
        (pResidual 2 C).map C.subtype = center SL) := by
  rcases h with ⟨c, hc, hA⟩ | ⟨c, σ, hσ, hc, hA⟩
  · have hz := factor_eq_center d.plusFactor d.sylow d.plus_perfect d.plus_quotient_card hA
    exact Or.inl ⟨c, hc, hz, graph_residual d hz⟩
  · have hz := factor_eq_center d.zeroFactor d.sylow d.zero_perfect d.zero_quotient_card hA
    exact Or.inr ⟨c, σ, hσ, hc, hz, graphField_residual d hz⟩

/-- The intrinsic marked SL₃(4) alternative, including the actual central
marked factor and the corresponding embedded two-residual comparison.
Standard-automorphism coverage is the sole additional classification premise. -/
theorem alternatives {α : MulAut SL} (d : MarkedBorelFactors α)
    (hcover : standard F = ⊤) :
    (∃ c : Matrix.GeneralLinearGroup (Fin 3) F,
      centerAction F α = linearConj F c * graph F ∧ d.plusFactor = center SL ∧
        let C := commutatorSubgroup (zpowers α) SL (normalizer (d.sylow : Set SL))
        (pResidual 2 C).map C.subtype = center SL) ∨
    (∃ (c : Matrix.GeneralLinearGroup (Fin 3) F) (σ : F ≃+* F),
      σ ≠ 1 ∧ centerAction F α = linearConj F c * fieldAction F σ * graph F ∧
        d.zeroFactor = center SL ∧
        let C := normalizer (d.sylow : Set SL) ⊓ α.fixedSubgroup
        (pResidual 2 C).map C.subtype = center SL) :=
  of_central_mod_sylow_alternatives d (central_mod_sylow_alternatives d hcover)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.IntrinsicAction
