module

public import ABG.ChapterII.Section3.QOddCoreQuotient
public import Theory.GroupTheory.PGroup.TrivialImage

/-!
# Enlarged Q-groups are not two-groups

A finite Q-group, and its odd-core quotient, cannot be a two-group. This
holds for the full enlarged definition, including quaternion Sylow subgroups.

The defining normal witness has no normal subgroup of index two, so every
homomorphism from it into a finite two-group is trivial. If the ambient group
were a two-group, its inclusion would make the witness trivial. The linked
Sylow intersection would then have trivial image, contradicting the actual
generalized quaternion subgroup in the defining overgroup. The odd-core
corollary uses the proved preservation of the enlarged Q predicate.

This supplies the non-complement exclusion in Alperin--Brauer--Gorenstein
II.3 Lemma 2, article page 24, before applying the dihedral classification.
-/

namespace ABG

public theorem IsQGroup.not_isPGroup
    {G : Type*} [Group G] [Finite G] (hG : IsQGroup G) : ¬ IsPGroup 2 G := by
  intro htwo
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, iS, _hS, R, f, Y, K, _hf, hY, _hKN, _hKi, hKno, _hw, hlink⟩ :=
    isQGroup_iff_quaternionOvergroup.mp hG
  let : Group S := iS
  have hKbot : K = ⊥ := by
    apply bot_unique
    intro x hx
    exact Subgroup.mem_bot.mpr
      (MonoidHom.eq_one_of_no_normal_index_prime hKno htwo K.subtype ⟨x, hx⟩)
  have hYbot : Y = ⊥ := by
    rw [hKbot, MonoidHom.comap_bot, (R : Subgroup G).ker_subtype,
      Subgroup.map_bot] at hlink
    exact hlink.symm
  obtain ⟨n, hn, ⟨e⟩⟩ := hY.1
  have hcard := Nat.card_congr e.toEquiv
  rw [hYbot, Subgroup.card_bot, Nat.card_eq_fintype_card, QuaternionGroup.card] at hcard
  have hpos : 0 < 2 ^ n := by positivity
  omega

public theorem IsQGroup.not_isPGroup_oddCore_quotient
    {G : Type*} [Group G] [Finite G] (hG : IsQGroup G) :
    ¬ IsPGroup 2 (G ⧸ pPrimeCore 2 G) :=
  hG.oddCore_quotient.not_isPGroup

end ABG
