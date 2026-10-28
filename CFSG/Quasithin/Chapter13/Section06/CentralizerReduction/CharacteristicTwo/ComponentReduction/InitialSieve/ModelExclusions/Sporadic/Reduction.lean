module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelInterface
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.QuotientAction

/-!
# Intrinsic Sylow-fixer inputs for the sporadic exclusion

The faithful four-group on the actual component image transports to the
literal two-core quotient model. Its elementary abelian structure contradicts
an intrinsic bound of two on pointwise Sylow fixers. Finiteness, simplicity,
perfectness and centerlessness of the model all come from this same quotient
isomorphism; no separate certification of the concrete carrier is required.

Source: Aschbacher–Smith, 1.1.5(3)(f), pp.501–503, and proof of 13.6.6,
printed p.927. These are conditional transfer results. Concrete bounds must
be supplied for every one of the ten sporadic alternatives.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.Sporadic
open A5Module

/-- The intrinsic model fact needed by the source's central four-group argument.
The simple and perfect instances are inherited from the genuine component. -/
def SmallSylowFixers (Q : Type*) [Group Q] : Prop :=
  ∀ [Finite Q] [IsSimpleGroup Q] [Group.IsPerfect Q]
    (P : Sylow 2 Q) (A : Subgroup (MulAut Q)) [IsElementaryAbelian 2 A],
    (∀ α ∈ A, ∀ x ∈ P, α x = x) → Nat.card A ≤ 2

theorem center_eq_bot_of_simple_perfect (Q : Type*) [Group Q]
    [IsSimpleGroup Q] [Group.IsPerfect Q] : center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) inferInstance with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp h)).elim

variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
  {s : Marking L V} {T : Sylow 2 G}

/-- Apply an intrinsic fixer bound to the actual quotient and the faithful action.
This includes nontrivial central covers of the concrete model. -/
theorem not_quotient_of_smallSylowFixers {Q : Type*} [Group Q]
    (hQ : SmallSylowFixers Q)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (a : ActionData s (T : Subgroup G) K) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Q) := by
  rintro ⟨e⟩
  let : IsQuasisimple K := hK.2
  let eQ := (NormalizerAction.componentCentralQuotientEquiv K).trans
    ((componentImageEquivTwoCoreQuotient K hK hodd).trans e)
  let : Finite Q := Finite.of_equiv _ eQ.toEquiv
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : IsSimpleGroup Q := eQ.symm.isSimpleGroup
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective (f := eQ.toMonoidHom) eQ.surjective
  obtain ⟨P, A, hA, hfix⟩ := exists_fixed_four_of_equiv K hK a
    ((componentImageEquivTwoCoreQuotient K hK hodd).trans e)
  let := hA
  let : IsElementaryAbelian 2 A := {
    toIsMulCommutative := IsKleinFour.isMulCommutative
    exponent_dvd_p := hA.exponent_two ▸ dvd_rfl }
  have hbound := hQ P A hfix
  rw [hA.card_four] at hbound
  omega

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.Sporadic
