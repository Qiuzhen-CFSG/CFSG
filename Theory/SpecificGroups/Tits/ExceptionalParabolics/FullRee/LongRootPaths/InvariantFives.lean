module
public import Theory.GroupTheory.NormalizedSylowTransitivity
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.FiveNormalizer

/-!
# Invariant fives in the actual full Ree first parabolic

The certified normalizer of the marked five has order80 and abelian
Sylow2 of order16. Its omega subgroup therefore controls all invariant
five-subgroups by the general Sylow normalizer argument. This concerns the
literal first endpoint and its original root marking, without recognizing
an arbitrary amalgam completion.
Source: Aschbacher--Smith J.4.10, first paragraph, printed p.444.
-/

public section
open Subgroup
open scoped Pointwise
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths.FiveNormalizer
open Theory.GroupTheory.NormalizedSylowTransitivity

private theorem five_le_first_model : five ≤ first := zpowers_le.mpr rotation_mem_first
private theorem I_le_first_model : I ≤ first := I_le_sylow.trans sylow_le_first

private theorem first_five_card : Nat.card (five.subgroupOf first) = 5 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe five_le_first_model).toEquiv]
  rw [five, Nat.card_zpowers, rotation_order]

private theorem first_I_card : Nat.card (I.subgroupOf first) = 16 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe I_le_first_model).toEquiv, I_card]

private theorem first_I_normalizes : I.subgroupOf first ≤
    normalizer ((five.subgroupOf first : Subgroup first) : Set first) := by
  rw [← subgroupOf_normalizer_eq five_le_first_model]
  exact fun _ hx => I_le_normalizer hx

private theorem first_normalizer_card' :
    Nat.card (normalizer ((five.subgroupOf first : Subgroup first) : Set first)) = 80 := by
  rw [← subgroupOf_normalizer_eq five_le_first_model]
  have he := Nat.card_congr ((fiveNormalizer.subgroupOf first).equivMapOfInjective
    first.subtype first.subtype_injective).toEquiv
  rw [subgroupOf_map_subtype] at he
  exact he.trans (by simpa only [inf_comm] using first_normalizer_card)

private theorem five_index_coprime (D : Subgroup first) (hD : Nat.card D = 5) : ¬ 5 ∣ D.index := by
  have hc := D.card_mul_index
  rw [hD, first_card] at hc
  have hi : D.index = 4096 := by omega
  rw [hi]
  decide

/-- Every invariant five is reached by an element normalizing the actual omega plane. -/
theorem exists_model_normalizing_conjugator (D : Subgroup first) (hD : Nat.card D = 5)
    (hn : Stellmacher.omegaOneCenterAmbient (I.subgroupOf first) ≤ normalizer (D : Set first)) :
    ∃ n ∈ normalizer (Stellmacher.omegaOneCenterAmbient (I.subgroupOf first) : Set first),
      (five.subgroupOf first).conjBy n = D := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let BP : Sylow 5 first := (IsPGroup.of_card (p := 5) (n := 1)
    (by simpa using first_five_card)).toSylow (five_index_coprime _ first_five_card)
  let DP : Sylow 5 first := (IsPGroup.of_card (p := 5) (n := 1)
    (by simpa using hD)).toSylow (five_index_coprime D hD)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq first BP DP
  have hg' : (five.subgroupOf first).conjBy g = D := congrArg Sylow.toSubgroup hg
  let I₀ := I.subgroupOf first
  obtain ⟨ei⟩ := I_equiv
  let e₀ := (subgroupOfEquivOfLe I_le_first_model).trans ei
  let : IsMulCommutative I₀ := IsMulCommutative.of_comm (fun x y => e₀.injective (by
    rw [map_mul,map_mul,mul_comm]))
  have hp : IsPGroup 2 I₀ := IsPGroup.of_card (p := 2) (n := 4) first_I_card
  have hi : ¬ 2 ∣ (I₀.subgroupOf (normalizer ((five.subgroupOf first : Subgroup first) : Set first))).index := by
    have hc := (I₀.subgroupOf (normalizer ((five.subgroupOf first : Subgroup first) : Set first))).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe first_I_normalizes).toEquiv,
      first_I_card,first_normalizer_card'] at hc
    have hh : (I₀.subgroupOf (normalizer ((five.subgroupOf first : Subgroup first) : Set first))).index = 5 := by omega
    rw [hh]
    decide
  obtain ⟨n,hnV,hnB⟩ := omega_conjugator (five.subgroupOf first) I₀
    first_I_normalizes hp hi g (hg'.symm ▸ hn)
  exact ⟨n,hnV,hnB.trans hg'⟩
end Tits.ExceptionalParabolics.FullRee.LongRootPaths.FiveNormalizer
