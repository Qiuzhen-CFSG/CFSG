module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.Sporadic.Reduction
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer
public import Theory.SpecificGroups.Rudvalis.Model.Primitive
public import Theory.GroupAction.AutomorphismNormalizer
public import Theory.GroupAction.ElementarySylowFixerBound

/-!
# The two remaining intrinsic Rudvalis inputs

The native permutation normalizer is already proved to equal Ru. Preservation
of the actual point-stabilizer class therefore makes every automorphism inner.
A bound of two on the centers of actual Sylow two-subgroups then bounds
elementary pointwise Sylow fixers by two. The two inputs are independent:
the local center calculation can be proved while the stabilizer-class
calculation is unfinished.

Source: GLS3 Table 5.3r and the sporadic exclusion in Aschbacher–Smith,
proof of 13.6.6, printed p.927. Simplicity and perfectness are inherited
from the component quotient by the consumer, rather than asserted for Ru.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.Sporadic

theorem rudvalis_smallSylowFixers_of_centers_and_stabilizers
    (hcenter : ∀ [IsSimpleGroup Rudvalis.Model] [Group.IsPerfect Rudvalis.Model]
      (P : Sylow 2 Rudvalis.Model), Nat.card (center P) ≤ 2)
    (hstable : ∀ [IsSimpleGroup Rudvalis.Model] [Group.IsPerfect Rudvalis.Model]
      (f : MulAut Rudvalis.Model), ∃ y : Fin 4060,
      (MulAction.stabilizer Rudvalis.Model (0 : Fin 4060)).map f.toMonoidHom =
        MulAction.stabilizer Rudvalis.Model y) :
    SmallSylowFixers Rudvalis.Model := by
  intro _ _ _ P A _ hfix
  let : IsCyclic (center P) := isCyclic_of_card_dvd_prime (p := 2) (by
    have hc := hcenter P
    have hp := Nat.card_pos (α := center P)
    have h : Nat.card (center P) = 1 ∨ Nat.card (center P) = 2 := by omega
    rcases h with h | h <;> simp [h])
  have hinner : Function.Surjective
      (MulAut.conj : Rudvalis.Model →* MulAut Rudvalis.Model) := by
    let : MulAction.IsPretransitive Rudvalis.modelSubgroup (Fin 4060) :=
      Rudvalis.model_isPretransitive
    exact Subgroup.conj_surjective_of_stabilizers_of_normalizer Rudvalis.modelSubgroup 0
      hstable Rudvalis.outer_permutation_normalizer_eq
  apply Theory.GroupAction.elementary_sylow_fixer_card_le_two_of_inner P
    (center_eq_bot_of_simple_perfect Rudvalis.Model) _ A hfix
  intro α _ _
  obtain ⟨g, hg⟩ := hinner α
  exact ⟨g, hg.symm⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.Sporadic
