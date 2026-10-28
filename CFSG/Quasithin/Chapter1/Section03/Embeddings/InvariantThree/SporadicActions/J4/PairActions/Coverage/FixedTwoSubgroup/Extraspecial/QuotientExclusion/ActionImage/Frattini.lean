module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.Conjugation
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel

/-!
# The three-part of the actual J₄ conjugation action on a Frattini quotient

For a subgroup K of the specified two-subgroup, passage from Aut(K) to
Aut(K/Φ(K)) has a two-group kernel. Thus divisibility by 27 is unchanged
when the actual normalizer action is composed with the Frattini action.
If K/Φ(K) has at most 32 elements, the order formula for GL(d,2), d ≤ 5,
already excludes 27 from the full automorphism group of K.

This proves the small-Frattini-quotient branch without a census or any
ambient normalizer calculation. It does not bound the Frattini quotient of
every large subgroup. Source context: the J₄ case of Aschbacher–Smith 1.3.4,
printed p.511/PDF p.528, and the Burnside basis-kernel theorem implemented
in `Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel`.
-/

@[expose] public section

open Subgroup
open Janko4.OuterReduction.OddIndex

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction

/-- The map retains exactly the automorphisms induced by the ambient normalizer. -/
noncomputable def fixedTwoFrattiniAction (K : Subgroup Janko4.Model) :
    normalizer (K : Set Janko4.Model) →* MulAut (K ⧸ frattini K) :=
  (quotientAut (frattini K)).comp K.normalizerMonoidHom

/-- The Frattini action loses only a two-group from the actual conjugation image. -/
theorem fixedTwoConjugation_not_dvd_twentySeven_iff_frattini
    {K : Subgroup Janko4.Model} (hKT : K ≤ twoSubgroup) :
    (¬ 27 ∣ Nat.card K.normalizerMonoidHom.range) ↔
      ¬ 27 ∣ Nat.card (fixedTwoFrattiniAction K).range := by
  let f := K.normalizerMonoidHom
  let ρ := quotientAut (frattini K)
  let r := ρ.comp f.range.subtype
  have hker : IsPGroup 2 r.ker := by
    let inclusion : r.ker →* ρ.ker :=
      (f.range.subtype.comp r.ker.subtype).codRestrict ρ.ker (fun x => x.property)
    apply (isPGroup_quotientAut_frattini_kernel
      (twoSubgroup_isPGroup.to_le hKT)).of_injective inclusion
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun z : ρ.ker => (z : MulAut K)) hxy))
  have hrange : r.range = (fixedTwoFrattiniAction K).range := by
    ext a
    constructor
    · rintro ⟨⟨_, g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨⟨f g, ⟨g, rfl⟩⟩, rfl⟩
  rw [← hrange]
  constructor
  · intro h hd
    exact h (hd.trans (card_range_dvd r))
  · intro h hd
    obtain ⟨n, hn⟩ := hker.exists_card_eq
    have hcop : Nat.Coprime 27 (Nat.card r.ker) := by
      rw [hn]
      exact (by decide : Nat.Coprime 27 2).pow_right n
    have hmul : Nat.card r.ker * Nat.card r.range = Nat.card f.range := by
      rw [← index_ker]
      exact r.ker.card_mul_index
    exact h (hcop.dvd_of_dvd_mul_left (hmul ▸ hd))

/-- The full automorphism bound for the small-Frattini-quotient branch. -/
theorem fixedTwoAut_not_dvd_twentySeven_of_smallFrattini
    {K : Subgroup Janko4.Model} (hKT : K ≤ twoSubgroup)
    (hsmall : Nat.card (K ⧸ frattini K) ≤ 32) :
    ¬ 27 ∣ Nat.card (MulAut K) := by
  have hp : IsPGroup 2 K := twoSubgroup_isPGroup.to_le hKT
  let _ : Fact (IsPGroup 2 K) := ⟨hp⟩
  let V := K ⧸ frattini K
  let _ : IsElementaryAbelian 2 V := isElementaryAbelian_quotient_frattini (p := 2)
  let f := quotientAut (frattini K)
  have hker : IsPGroup 2 f.ker := isPGroup_quotientAut_frattini_kernel hp
  obtain ⟨n, hn⟩ := (hp.to_quotient (frattini K)).exists_card_eq
  have hle : n ≤ 5 := by
    by_contra! hh
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    rw [← hn] at hpow
    norm_num at hpow
    omega
  have haut : ¬ 27 ∣ Nat.card (MulAut V) := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow V n hn]
    interval_cases n <;> norm_num [Fin.prod_univ_succ]
  obtain ⟨k, hk⟩ := hker.exists_card_eq
  have hcop : Nat.Coprime 27 (Nat.card f.ker) := by
    rw [hk]
    exact (by decide : Nat.Coprime 27 2).pow_right k
  have hmul : Nat.card f.ker * Nat.card f.range = Nat.card (MulAut K) := by
    rw [← index_ker]
    exact f.ker.card_mul_index
  intro hd
  rw [← hmul] at hd
  exact haut ((hcop.dvd_of_dvd_mul_left hd).trans f.range.card_subgroup_dvd_card)

/-- A small Frattini quotient suffices for the actual ambient image as well. -/
theorem fixedTwoConjugation_not_dvd_twentySeven_of_smallFrattini
    {K : Subgroup Janko4.Model} (hKT : K ≤ twoSubgroup)
    (hsmall : Nat.card (K ⧸ frattini K) ≤ 32) :
    ¬ 27 ∣ Nat.card K.normalizerMonoidHom.range :=
  fixedTwoLargeConjugation_not_dvd_twentySeven_of_aut
    (fixedTwoAut_not_dvd_twentySeven_of_smallFrattini hKT hsmall)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
