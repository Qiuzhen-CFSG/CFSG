module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveOrdinaryTable

/-!
# Sylow and central averages of the Lyons local character table

On the Sylow subgroup the linear rows sum to 64, while the quartic and
quintic rows sum to zero. On its center the corresponding sums are 4, 0
and 20. The quartic calculation uses its two positive and two negative
central values; the quintic calculation uses its nonprincipal inducing
linear character. These averages provide the principal-block counting
argument without conjugacy-class enumeration.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972),
Lemmas 2 and 4, pp. 373 and 381.
-/

public section

noncomputable section
open scoped BigOperators

open Stellmacher.Recognition.LyonsU3Four
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace Stellmacher.Recognition.LyonsU3Four
variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    {α : FiveComplement →* MulAut S}

private theorem quartic_sum (T : LocalFiveCharacterTable S α) (z : QuarticCentralIndex S) :
    ∑ s : S, T.sylowQuartic z (ConjClasses.mk s) = 0 := by
  obtain ⟨n, ρ, he⟩ := (T.sylow_spec z).irreducible.1
  have hi : IsIrreducibleCharacter (ofConjClassFunction (T.sylowQuartic z)) := by
    refine ⟨n, ρ, ?_, ?_⟩
    · exact (irreducible_iff_character_norm_one ρ).mpr (he ▸ (T.sylow_spec z).irreducible.2)
    · rw [he]; rfl
  apply (scalarProduct_principal_eq_zero_iff _).mp
  apply hi.scalarProduct_principal_eq_zero
  intro heq
  have hd := congrFun heq 1
  change T.sylowQuartic z (ConjClasses.mk 1) = 1 at hd
  rw [(T.sylow_spec z).degree] at hd
  norm_num at hd

private theorem quintic_sum (T : LocalFiveCharacterTable S α) (i : Fin 3) :
    ∑ s : S, T.row (.inr (.inr i)) (ConjClasses.mk (SemidirectProduct.inl s)) = 0 := by
  simp_rw [T.quintic_restriction]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a _
  have hr : (∑ x : S, T.quinticSeed i (α a x)) = ∑ x : S, T.quinticSeed i x :=
    (α a).toEquiv.sum_comp (fun x => T.quinticSeed i x)
  rw [hr]
  apply (scalarProduct_principal_eq_zero_iff _).mp
  apply (T.quinticSeed i).isLinearCharacter.1.scalarProduct_principal_eq_zero
  exact fun he => T.seed_nontrivial i (DFunLike.coe_injective he)

private theorem quartic_center_sum (h : SylowStructure S)
    (T : LocalFiveCharacterTable S α) (z : QuarticCentralIndex S) :
    ∑ w : Subgroup.center S, T.sylowQuartic z (ConjClasses.mk (w : S)) = 0 := by
  have hv (w : Subgroup.center S) :
      T.sylowQuartic z (ConjClasses.mk (w : S)) =
        8 * (if w = 1 then (1 : ℂ) else 0) +
        8 * (if w = z.1 then (1 : ℂ) else 0) - 4 := by
    rw [(T.sylow_spec z).value]
    have he1 : (w : S) = 1 ↔ w = 1 :=
      ⟨fun hh => Subtype.ext hh, fun hh => congrArg Subtype.val hh⟩
    have hez : (w : S) = z.1.1 ↔ w = z.1 := Subtype.ext_iff.symm
    simp only [he1, hez]
    by_cases hw : w = 1
    · subst w; norm_num [Ne.symm z.2]
    · by_cases hwz : w = z.1 <;> norm_num [hw, hwz, w.property, z.2]
  simp_rw [hv]
  norm_num [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Nat.card_eq_fintype_card, h.center_card]

theorem LocalFiveCharacterTable.sum_sylow (h : SylowStructure S) (T : LocalFiveCharacterTable S α)
    (i : LocalFiveRowIndex S) :
    ∑ s : S, T.row i (ConjClasses.mk (SemidirectProduct.inl s)) =
      match i with | .inl _ => 64 | _ => 0 := by
  rcases i with χ | (⟨z, χ⟩ | i)
  · simp [T.linear_value, ← Nat.card_eq_fintype_card, h.card]
  · change (∑ s : S, localFiveQuarticTwist S α (T.quartic z) χ
      (ConjClasses.mk (SemidirectProduct.inl s))) = 0
    simp_rw [localFiveQuarticTwist_restriction (T.extension_spec z)]
    exact quartic_sum T z
  · exact quintic_sum T i

theorem LocalFiveCharacterTable.sum_center (h : SylowStructure S) (T : LocalFiveCharacterTable S α)
    (i : LocalFiveRowIndex S) :
    ∑ w : Subgroup.center S, T.row i (ConjClasses.mk (SemidirectProduct.inl (w : S))) =
      match i with | .inl _ => 4 | .inr (.inl _) => 0 | .inr (.inr _) => 20 := by
  rcases i with χ | (⟨z, χ⟩ | i)
  · simp [T.linear_value, ← Nat.card_eq_fintype_card, h.center_card]
  · change (∑ w : Subgroup.center S, localFiveQuarticTwist S α (T.quartic z) χ
      (ConjClasses.mk (SemidirectProduct.inl (w : S)))) = 0
    simp_rw [localFiveQuarticTwist_restriction (T.extension_spec z)]
    exact quartic_center_sum h T z
  · change (∑ w : Subgroup.center S, localFiveQuintic S α (T.quinticSeed i)
      (ConjClasses.mk (SemidirectProduct.inl (w : S)))) = 20
    norm_num [localFiveQuintic_central_value S α h, ← Nat.card_eq_fintype_card, h.center_card]

end Stellmacher.Recognition.LyonsU3Four
