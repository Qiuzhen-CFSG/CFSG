module

public import Theory.SpecificGroups.Tits.RelativeSecondBlockLayers
public import Theory.GroupTheory.SmallIndexSolvable
public import Theory.GroupTheory.Fitting.Centralizer

/-!
# Characteristic two in the second Tits parabolic

Its Sylow two-subgroup has index three, so the parabolic is solvable.
The odd core has order dividing three. If nontrivial, it contains the
specified order-three rotation and commutes with the two-core, contradicting
the checked action on the square of the root generator. Thus the odd core
is trivial; solvable Fitting self-centralization gives the result.

Source: the local condition needed for Aschbacher–Smith, Theorem 0.1.2(1),
printed pp.3–4 and 481–482. The actual words, order and core-action witness
are from the certified Parrott model, following Parrott (1972), p.683.
No full parabolic quotient identification is needed.
-/

namespace Tits.ConverseLocalCores
open Subgroup ExceptionalParabolics RelativeSecondBlockLayers
open scoped commutatorElement

private theorem second_solvable : Group.IsSolvable second := by
  have hS : IsPGroup 2 S := IsPGroup.of_card (n := 11) (by simpa using sylow_card)
  let : Group.IsNilpotent (S.subgroupOf second) := hS.comap_subtype.isNilpotent
  apply (S.subgroupOf second).isSolvable_of_index_le_four
  rw [second_sylow_index]
  decide

private def rotationSylow : Sylow 3 second :=
  Sylow.ofCard (zpowers rotation) (by
    rw [Nat.card_zpowers, rotation_order, second_card]
    decide +kernel)

private theorem odd_core_eq_bot : pPrimeCore 2 second = ⊥ := by
  let O := pPrimeCore 2 second
  have hcop : Nat.Coprime (Nat.card O) (2 ^ 11) :=
    (pPrimeCore_coprime_card (p := 2) (G := second)).symm.pow_right 11
  have hdiv : Nat.card O ∣ 2 ^ 11 * 3 := by
    simpa only [second_card, show 2 ^ 11 * 3 = 6144 by norm_num]
      using O.card_subgroup_dvd_card
  have hdiv3 : Nat.card O ∣ 3 := hcop.dvd_of_dvd_mul_left hdiv
  rcases (Nat.dvd_prime Nat.prime_three).mp hdiv3 with hone | hthree
  · exact Subgroup.card_eq_one.mp hone
  · have hO3 : IsPGroup 3 O := IsPGroup.of_card (p := 3) (n := 1) (by simpa using hthree)
    have hOP : O = (rotationSylow : Subgroup second) :=
      eq_of_le_of_card_ge (hO3.le_sylow_of_normal rotationSylow) (by
        change Nat.card (zpowers rotation) ≤ Nat.card O
        rw [Nat.card_zpowers, rotation_order, hthree])
    have hr : rotation ∈ O := by rw [hOP]; exact mem_zpowers rotation
    have hdis : Disjoint (pCore 2 second) O :=
      IsPGroup.disjoint_of_ne 2 3 (by decide) _ _ pCore_isPGroup hO3
    have hcent : pCore 2 second ≤ centralizer (O : Set second) :=
      commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hdis)
    have hc := mem_centralizer_iff.mp (hcent root_square_mem_core) rotation hr
    exfalso
    apply root_square_commutator_square_ne_one
    have he : ⁅rootElement ^ 2, rotation⁆ = 1 := by
      apply commutatorElement_eq_one_iff_mul_comm.mpr
      exact hc.symm
    rw [he, one_pow]

/-- The intrinsic two-core of the actual second parabolic is self-centralizing. -/
public theorem second_core_self_centralizing :
    centralizer (pCore 2 second : Set second) ≤ pCore 2 second := by
  have hfit : fittingSubgroup second = pCore 2 second :=
    Fitting_eq_pcore second 2 odd_core_eq_bot
  rw [← hfit]
  exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable second_solvable
end Tits.ConverseLocalCores
