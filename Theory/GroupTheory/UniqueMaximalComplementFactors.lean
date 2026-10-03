module

public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.Order.Atoms.Finite

/-!
# Unique maximal overgroups and normal complement factors

Let D and C be disjoint normal subgroups of a finite group. Suppose their
join has a disjoint supplement S, and S lies in exactly one maximal
subgroup. Then one of D and C is trivial. Neither a Sylow assumption nor
an odd-order assumption is needed once disjoint supplementation is given.

If D joined with S were the whole group, the normal-join cardinal formula
would give D = D joined with C, forcing C to be trivial. Thus when both
factors are nontrivial, each joined with S is proper. The unique maximal
overgroup contains both proper joins, contradicting full generation.
Normality of both factors in the full group is essential to this argument.

This bounded complement argument is used to remove the odd centralizer
factor from the canonical product in Stellmacher (9.10)(3), printed p.57
of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Subgroup

private theorem factor_eq_of_sup_eq_top
    {G : Type*} [Group G] [Finite G]
    (D W S : Subgroup G) [D.Normal] [W.Normal]
    (hDW : D ≤ W) (hWS : Disjoint W S)
    (hWSgen : W ⊔ S = ⊤) (hDSgen : D ⊔ S = ⊤) : D = W := by
  have hDS : Disjoint D S := hWS.mono hDW le_rfl
  have hWcard := card_mul_eq_card_inf_mul_card_sup_of_normalizes W S
    (by rw [normalizer_eq_top]; exact le_top)
  have hDcard := card_mul_eq_card_inf_mul_card_sup_of_normalizes D S
    (by rw [normalizer_eq_top]; exact le_top)
  rw [hWS.eq_bot, hWSgen, card_bot, one_mul] at hWcard
  rw [hDS.eq_bot, hDSgen, card_bot, one_mul] at hDcard
  exact eq_of_le_of_card_ge hDW
    (Nat.mul_right_cancel (Nat.card_pos (α := S)) (hDcard.trans hWcard.symm)).ge

public theorem eq_bot_or_eq_bot_of_normal_complement_unique_maximal
    {G : Type*} [Group G] [Finite G]
    (D C S : Subgroup G) [D.Normal] [C.Normal]
    (hDC : Disjoint D C) (hWS : Disjoint (D ⊔ C) S)
    (hgen : (D ⊔ C) ⊔ S = ⊤)
    (hunique : ∃! M : Subgroup G, IsCoatom M ∧ S ≤ M) :
    D = ⊥ ∨ C = ⊥ := by
  by_contra hboth
  push Not at hboth
  obtain ⟨hD, hC⟩ := hboth
  obtain ⟨M, ⟨hM, hSM⟩, huniq⟩ := hunique
  have hproper (K : Subgroup G) (hSK : S ≤ K) (hK : K ≠ ⊤) : K ≤ M := by
    obtain ⟨N, hN, hKN⟩ := (eq_top_or_exists_le_coatom K).resolve_left hK
    exact (huniq N ⟨hN, hSK.trans hKN⟩) ▸ hKN
  have hDS : D ⊔ S ≠ ⊤ := by
    intro htop
    have hDall := factor_eq_of_sup_eq_top D (D ⊔ C) S le_sup_left hWS hgen htop
    have hCD : C ≤ D := le_sup_right.trans hDall.ge
    exact hC (bot_unique ((le_inf hCD le_rfl).trans hDC.eq_bot.le))
  have hCS : C ⊔ S ≠ ⊤ := by
    intro htop
    have hCall := factor_eq_of_sup_eq_top C (D ⊔ C) S le_sup_right hWS hgen htop
    have hDC' : D ≤ C := le_sup_left.trans hCall.ge
    exact hD (bot_unique ((le_inf le_rfl hDC').trans hDC.eq_bot.le))
  have hDM : D ≤ M := le_sup_left.trans (hproper (D ⊔ S) le_sup_right hDS)
  have hCM : C ≤ M := le_sup_left.trans (hproper (C ⊔ S) le_sup_right hCS)
  apply hM.ne_top
  exact top_unique (hgen ▸ sup_le (sup_le hDM hCM) hSM)

end Subgroup
