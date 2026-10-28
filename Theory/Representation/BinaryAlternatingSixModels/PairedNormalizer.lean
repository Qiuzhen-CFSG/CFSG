module
public import Theory.Representation.BinaryAlternatingSixModels.PairedHeads
public import Theory.Representation.SixLetterTransvections
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ElementaryOuter
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Transport

/-!
# The paired A₆ movement obstruction for the full normalizer

The two inequivalent natural heads cost at least four dimensions on every
nonidentity component element. For a self-centralizing normal A₆, a putative
transvection has component commutators moving at most two dimensions; all
such commutators therefore vanish, contradicting self-centralization.
An elementary actor has at most two cosets modulo the component and has
rank at most three. If it meets the component, it costs at least four;
otherwise it has rank at most one and costs at least two. Thus no FF
offender occurs, including outside the component.

The Chapter 13 consumer supplies the movement bound from its two actual
quotient maps and uses the full two-core action quotient. This proves the
ordinary Thompson step, without assuming an extension of the two natural
heads to the whole actor. Source: Aschbacher--Smith 13.4.7, pp.900--901.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix BinaryDuadModule
namespace BinaryAlternatingSix

/-- Each of the two natural modules costs at least two on a nonidentity element. -/
theorem paired_natural_movement (a : A6) (ha : a ≠ 1) :
    4 ≤ fixedCodim firstAlternating (zpowers a) +
      fixedCodim secondAlternating (zpowers a) := by
  have hf : Function.Injective firstAlternating := by
    intro x y he
    apply Subtype.ext
    apply polarRepresentation_injective
    apply Subtype.ext
    exact congrArg LinearMap.toMatrix' he
  have hs : Function.Injective secondAlternating := by
    intro x y he
    apply alternatingDiagramAut.injective
    apply hf
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun he v
  have h1 : 2 ≤ fixedCodim firstAlternating (zpowers a) := by
    by_contra hn
    exact ha (Representation.SixLetterTransvections.alternating_eq_one_of_displacement_le_one
      firstAlternating hf a (by rw [←fixedCodim_zpowers_eq_displacement_rank]; omega))
  have h2 : 2 ≤ fixedCodim secondAlternating (zpowers a) := by
    by_contra hn
    exact ha (Representation.SixLetterTransvections.alternating_eq_one_of_displacement_le_one
      secondAlternating hs a (by rw [←fixedCodim_zpowers_eq_displacement_rank]; omega))
  omega

variable {H M : Type*} [Group H]
  [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]

private theorem elementary_card_bound
    (K : Subgroup H) [K.Normal] (e : K ≃* A6)
    (hc : centralizer (K : Set H) = ⊥)
    (B : Subgroup H) [IsElementaryAbelian 2 B] :
    Nat.card B ≤ 2 * Nat.card (B.subgroupOf K) := by
  let f := AlternatingSix.ShadowLocal.conjugationAction K e
  let : IsElementaryAbelian 2 (B.map f) := IsElementaryAbelian.map f
  have hpre : AlternatingSix.ShadowLocal.inner.comap f = K := by
    rw [AlternatingSix.ShadowLocal.conjugationAction_preimage_inner,hc,sup_bot_eq]
  have hi : K.relIndex B ≤ 2 := by
    rw [←hpre,relIndex_comap]
    exact AlternatingSix.ShadowLocal.elementary_inner_relIndex (B.map f)
  have hk : Nat.card (K.subgroupOf B) = Nat.card (B.subgroupOf K) := by
    calc
      _ = Nat.card ((K.subgroupOf B).map B.subtype) :=
        (card_map_of_injective B.subtype_injective).symm
      _ = Nat.card ((B.subgroupOf K).map K.subtype) := by
        rw [subgroupOf_map_subtype,subgroupOf_map_subtype,inf_comm]
      _ = _ := card_map_of_injective K.subtype_injective
  have hm := (K.subgroupOf B).card_mul_index
  change Nat.card (K.subgroupOf B) * K.relIndex B = Nat.card B at hm
  rw [hk] at hm
  nlinarith

/-- A self-centralizing normal A₆ whose nonidentity elements move at least four
has no FF offender, including actors outside the component. -/
theorem not_ff_of_component_movement
    (ρ : Representation (ZMod 2) H M)
    (K : Subgroup H) [K.Normal] (e : K ≃* A6)
    (hc : centralizer (K : Set H) = ⊥)
    (hm : ∀ k : K, k ≠ 1 → 4 ≤ fixedCodim ρ (zpowers (k : H))) :
    ¬ IsFFModule ρ := by
  have htwo (a : H) (ha : a ≠ 1) : 2 ≤ fixedCodim ρ (zpowers a) := by
    by_contra hn
    have hcent : a ∈ centralizer (K : Set H) := by
      apply mem_centralizer_iff.mpr
      intro t ht
      have hmem : a*t*a⁻¹*t⁻¹ ∈ K := K.mul_mem
        ((inferInstance : K.Normal).conj_mem _ ht a) (K.inv_mem ht)
      have hu := fixedCodim_commutator_le_twice ρ a t
      have he : a*t*a⁻¹*t⁻¹ = 1 := by
        by_contra he
        have hl := hm ⟨_,hmem⟩ (fun hh => he (congrArg Subtype.val hh))
        change 4 ≤ fixedCodim ρ (zpowers (a*t*a⁻¹*t⁻¹)) at hl
        omega
      have he' := congrArg (fun x : H => x*(t*a)) he
      have hh : a*t = t*a := by
        simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one,one_mul] using he'
      exact hh.symm
    exact ha (mem_bot.mp (hc ▸ hcent))
  rintro ⟨B,hB⟩
  let := hB.1.2
  let I := B.subgroupOf K
  let : IsElementaryAbelian 2 I := IsElementaryAbelian.comap_of_injective K.subtype
    K.subtype_injective B
  let : IsElementaryAbelian 2 (I.map e.toMonoidHom) := IsElementaryAbelian.map e.toMonoidHom
  have hcard : Nat.card B ≤ 2 * Nat.card I := elementary_card_bound K e hc B
  have hi : Nat.card I ≤ 4 := by
    by_cases hz : I.map e.toMonoidHom = ⊥
    · have hh : I = ⊥ := (map_eq_bot_iff_of_injective I e.injective).mp hz
      rw [hh,card_bot]; omega
    · have hr := elementary_rank_le_two (I.map e.toMonoidHom)
      have he := (show IsElementaryTwo (I.map e.toMonoidHom) from ⟨hz,inferInstance⟩).card_eq_two_pow_rank
      rw [card_map_of_injective e.injective] at he
      exact he.trans_le (by simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr)
  have hr : rank B ≤ 3 := (Nat.log_monotone (b := 2) (show Nat.card B ≤ 8 by omega)).trans (by decide)
  by_cases hz : I = ⊥
  · rw [hz,card_bot] at hcard
    have hr1 : rank B ≤ 1 := (Nat.log_monotone (b := 2) (show Nat.card B ≤ 2 by omega)).trans (by decide)
    obtain ⟨b,hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB.1.1
    have h2 := htwo b (fun hh => hb (Subtype.ext hh))
    have hbB : zpowers (b : H) ≤ B := zpowers_le.mpr b.property
    have hu := Submodule.finrank_mono (fixedSpace_antitone ρ hbB)
    have hdim := fixedCodim_add_finrank ρ B
    have hdimb := fixedCodim_add_finrank ρ (zpowers (b : H))
    have hf := hB.2
    omega
  · obtain ⟨k,hk⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hz
    have h4 := hm k.val (fun hh => hk (Subtype.ext hh))
    have hkB : zpowers (k.val : H) ≤ B := zpowers_le.mpr k.property
    change 4 ≤ fixedCodim ρ (zpowers (k.val : H)) at h4
    have hu := Submodule.finrank_mono (fixedSpace_antitone ρ hkB)
    have hdim := fixedCodim_add_finrank ρ B
    have hdimk := fixedCodim_add_finrank ρ (zpowers (k.val : H))
    have hf := hB.2
    omega
end BinaryAlternatingSix
