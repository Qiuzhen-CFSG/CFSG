module

public import Theory.SpecificGroups.Alternating.SevenFiveSeed
public import Theory.SpecificGroups.Alternating.SevenFivePlacement.ThreeCycles
public import Theory.Representation.BinaryAlternatingSevenControl.Offenders

/-!
# Five-letter seeds through the binary A₇ offender

A four-group centralizing a three-cycle fixes at least a plane: a nonzero
fixed vector and its cubic translate are independent over the binary field.
It is therefore a best offender. Transport the concrete five-letter seed
along Sylow conjugacy and use uniqueness of the best offender in a Sylow.

Source: Aschbacher–Smith C.1.24, printed pp.130–131, exceptional A₇ case.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped Pointwise
namespace Representation.AlternatingSevenFiveSeed
open BinaryAlternatingSevenControl
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The complementary cubic certifies the four-point Klein group as a best offender. -/
theorem best_of_central_cubic (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (A : Subgroup A7) (hel : IsElementaryAbelian 2 A) (hcard : Nat.card A = 4)
    (c : A7) (hc : c ∈ centralizer (A : Set A7))
    (hthree : (c : Equiv.Perm (Fin 7)).IsThreeCycle) : IsBestOffender ρ A := by
  let := hel
  have hA : IsElementaryTwo A := ⟨by
    intro he
    rw [he,card_bot] at hcard
    omega,hel⟩
  have hr : rank A = 2 := by
    rw [rank,hcard]
    decide
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega :
    0 < Module.finrank (ZMod 2) V)
  obtain ⟨v,hv,hfix⟩ := BinaryLinearThree.IrreducibleCatalogue.binary_pGroup_fixed_vector
    (ρ.comp A.subtype) (IsElementaryAbelian.isPGroup 2 A)
  have hcv : ρ c v ∈ fixedSpace ρ A := by
    intro a
    change ρ (a : A7) (ρ c v) = ρ c v
    rw [← Module.End.mul_apply,← map_mul,hc a a.property,map_mul,Module.End.mul_apply]
    exact congrArg (ρ c) (hfix a)
  have hne : ρ c v ≠ v := fun he => hv
    (binaryAlternatingSeven_threeCycle_fixedPointFree ρ hf hd c hthree v he)
  let w : fixedSpace ρ A := ⟨v,hfix⟩
  let z : fixedSpace ρ A := ⟨ρ c v,hcv⟩
  have hli : LinearIndependent (ZMod 2) ![z,w] := by
    rw [linearIndependent_fin2]
    constructor
    · exact fun he => hv (congrArg Subtype.val he)
    · intro a
      fin_cases a
      · change (0 : ZMod 2) • w ≠ z
        rw [zero_smul]
        intro he
        have hz : ρ c v = 0 := (congrArg Subtype.val he).symm
        exact hv (by simpa only [ρ.inv_self_apply,map_zero] using congrArg (ρ c⁻¹) hz)
      · change (1 : ZMod 2) • w ≠ z
        rw [one_smul]
        exact fun he => hne (congrArg Subtype.val he).symm
  have hd2 : 2 ≤ Module.finrank (ZMod 2) (fixedSpace ρ A) := by
    simpa using hli.fintype_card_le_finrank
  apply (isBestOffender_iff_of_not_strong ρ (no_strong_offender ρ hf hd) A).mpr
  refine ⟨hA,?_⟩
  have hh := fixedCodim_add_finrank ρ A
  have hl := elementary_two_le_codim ρ hf hd hA
  omega

/-- A five-letter subgroup normalized by a full Sylow has no nonzero fixed
vector on either faithful binary A₇ four-space. -/
theorem five_fixedSpace_eq_bot (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (B : Subgroup A7) (e : B ≃* alternatingGroup (Fin 5))
    (R : Sylow 2 A7) (hBN : (R : Subgroup A7) ≤ normalizer (B : Set A7)) :
    fixedSpace ρ B = ⊥ := by
  have hcard : Nat.card B = 60 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  obtain ⟨c,hc⟩ := exists_prime_orderOf_dvd_card' (G := B) 3 (by rw [hcard]; decide)
  have hthree := Theory.SpecificGroups.Alternating.SevenFivePlacement.isThreeCycle_of_order_three
    B e R hBN c hc
  apply bot_unique
  intro v hv
  exact binaryAlternatingSeven_threeCycle_fixedPointFree ρ hf hd c.val hthree v (hv c)

/-- The selected five-letter group moves the actual fixed plane of the offender,
the noncentrality needed by the exceptional C.1.24 local seed. -/
theorem five_moves_offender_fixedSpace (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (B : Subgroup A7) (e : B ≃* alternatingGroup (Fin 5))
    (R : Sylow 2 A7) (hBN : (R : Subgroup A7) ≤ normalizer (B : Set A7))
    (A : Subgroup A7) (hA : IsBestOffender ρ A) :
    ∃ b ∈ B, ∃ v ∈ fixedSpace ρ A, ρ b v ≠ v := by
  have hdA := (best_dimensions ρ hf hd hA).2.2
  have hn : fixedSpace ρ A ≠ ⊥ := by
    intro he
    rw [he,finrank_bot] at hdA
    omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  by_contra! hall
  have hfix : v ∈ fixedSpace ρ B := fun b => hall b b.property v hv
  rw [five_fixedSpace_eq_bot ρ hf hd B e R hBN] at hfix
  exact hv0 hfix

/-- Every best offender in the supplied Sylow lies as a Sylow four-group in
an actual five-letter subgroup normalized by that same Sylow. This subgroup
escapes the offender normalizer and generates A₇ with it. -/
theorem exists_five_seed (ρ : Representation (ZMod 2) A7 V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (R : Sylow 2 A7) (A : Subgroup A7) (hAR : A ≤ R)
    (hA : IsBestOffender ρ A) :
    ∃ B : Subgroup A7, Nonempty (B ≃* alternatingGroup (Fin 5)) ∧
      (R : Subgroup A7) ≤ normalizer (B : Set A7) ∧ A ≤ B ∧
      (∃ P : Sylow 2 B, (P : Subgroup B).map B.subtype = A) ∧
      ¬ B ≤ normalizer (A : Set A7) ∧ normalizer (A : Set A7) ⊔ B = ⊤ ∧
      ∃ i j : Fin 7, i ≠ j ∧ B = fixingSubgroup A7 ({i,j} : Set (Fin 7)) := by
  classical
  let A₀ := Theory.SpecificGroups.Alternating.SevenFiveSeed.four
  let B₀ := Theory.SpecificGroups.Alternating.SevenFiveSeed.five
  let R₀ := Theory.SpecificGroups.Alternating.SevenFiveSeed.sylow
  have hbest : IsBestOffender ρ A₀ := best_of_central_cubic ρ hf hd A₀
    Theory.SpecificGroups.Alternating.SevenFiveSeed.four_elementary
    Theory.SpecificGroups.Alternating.SevenFiveSeed.four_card
    Theory.SpecificGroups.Alternating.SevenFiveSeed.cubic
    Theory.SpecificGroups.Alternating.SevenFiveSeed.cubic_centralizes_four
    Theory.SpecificGroups.Alternating.SevenFiveSeed.cubic_threeCycle
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A7 R₀ R
  let e := MulAut.conj g
  let f := e.toMonoidHom
  have hR : (R₀ : Subgroup A7).map f = R := congrArg Sylow.toSubgroup hg
  have hA₀R : A₀.map f ≤ R := by
    rw [←hR]
    exact map_mono Theory.SpecificGroups.Alternating.SevenFiveSeed.four_le_sylow
  have hAeq : A₀.map f = A := best_unique_in_sylow ρ hf hd R hA₀R hAR
    (hbest.map_conj ρ g) hA
  let B := B₀.map f
  let eB : B ≃* alternatingGroup (Fin 5) :=
    (B₀.equivMapOfInjective f e.injective).symm.trans
      Theory.SpecificGroups.Alternating.SevenFiveSeed.fiveEquiv
  have hBN : (R : Subgroup A7) ≤ normalizer (B : Set A7) := by
    rw [←hR,←B₀.map_normalizer_eq_of_bijective e.bijective]
    exact map_mono Theory.SpecificGroups.Alternating.SevenFiveSeed.sylow_normalizes_five
  have hAB : A ≤ B := by
    rw [←hAeq]
    exact map_mono Theory.SpecificGroups.Alternating.SevenFiveSeed.four_le_five
  have hcardA : Nat.card A = 4 := (best_dimensions ρ hf hd hA).2.1
  have hcardB : Nat.card B = 60 := by
    rw [Nat.card_congr eB.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  let P : Sylow 2 B := Sylow.ofCard (A.subgroupOf B) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAB).toEquiv,hcardA,hcardB]
    decide +kernel)
  have hgen : normalizer (A : Set A7) ⊔ B = ⊤ := by
    have hh := congrArg (Subgroup.map f)
      Theory.SpecificGroups.Alternating.SevenFiveSeed.normalizer_sup_five
    rw [Subgroup.map_sup,A₀.map_normalizer_eq_of_bijective e.bijective,hAeq,
      map_top_of_surjective f e.surjective] at hh
    exact hh
  have hn : ¬ B ≤ normalizer (A : Set A7) := by
    intro hn
    apply Theory.SpecificGroups.Alternating.SevenFiveSeed.five_not_le_normalizer
    apply (map_le_map_iff_of_injective (f := f) e.injective).mp
    change B ≤ (normalizer (A₀ : Set A7)).map f
    rw [A₀.map_normalizer_eq_of_bijective e.bijective,hAeq]
    exact hn
  exact ⟨B,⟨eB⟩,hBN,hAB,⟨P,map_subgroupOf_eq_of_le hAB⟩,hn,hgen,
    Theory.SpecificGroups.Alternating.SevenFivePlacement.exists_fixed_pair B eB R hBN⟩

end Representation.AlternatingSevenFiveSeed
