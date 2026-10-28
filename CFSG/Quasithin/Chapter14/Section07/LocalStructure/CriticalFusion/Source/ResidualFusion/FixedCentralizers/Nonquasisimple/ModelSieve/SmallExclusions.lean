module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.QuotientInputs

/-!
# Two model exclusions for the fixed component in 14.7.68

The proper image of K in Lᵤ/O₂(Lᵤ) has A₅ as its own two-core quotient.
Consequently Lᵤ/O₂(Lᵤ) cannot itself be A₅: its subgroup would already
have at least the order of the whole group. This excludes C.2.7(3)(a)(ii)
and the degree-five case of (b).

For (c), the actual A-hat₆ core quotient has order 1080, with only one
factor of five. An index-fifteen intersection containing K would force a
second factor of five in Lᵤ. Its two-core cannot supply that factor.

These exclude two source alternatives; they do not complete the comparison
with A.3.14 or assert the three-model conclusion.
Source: Aschbacher–Smith, combined manuscript (1 March 2004),
C.2.7(3), pp.145–147, and 14.7.68(2), pp.1071–1072.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

/-- An A₅ core quotient leaves no room for the strict K-image. -/
theorem fixedComponent_core_not_alternatingFive (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu)
    (hm : Nonempty ((Lu ⧸ pCore 2 Lu) ≃* alternatingGroup (Fin 5))) : False := by
  obtain ⟨e⟩ := hm
  let B := ((K F).subgroupOf Lu).map (QuotientGroup.mk' (pCore 2 Lu))
  have hcard : Nat.card (Lu ⧸ pCore 2 Lu) = Nat.card (B ⧸ pCore 2 B) :=
    (Nat.card_congr e.toEquiv).trans
      (Nat.card_congr (d.KImageCoreAlternatingFive Lu h.larger.le).toEquiv).symm
  have hle : Nat.card (Lu ⧸ pCore 2 Lu) ≤ Nat.card B :=
    hcard.le.trans (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _))
  have htop : B = ⊤ := B.eq_top_of_card_eq
    (le_antisymm (Nat.card_le_card_of_injective B.subtype B.subtype_injective) hle)
  exact (d.fixedComponent_core_K_image_lt_top u h).ne htop

/-- This discharges the A₅ model in C.2.7(3)(a)(ii) and (b). -/
theorem fixedComponent_not_alternatingFiveBlock (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) (hm : ChapterC.IsAlternatingBlock Lu 5) : False :=
  d.fixedComponent_core_not_alternatingFive u h hm.2.2.quotient_iso

/-- The source intersection contains an element of order divisible by five,
as witnessed by the actual A₅ quotient of K. -/
theorem fixedComponent_five_dvd_inter_card (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) :
    5 ∣ Nat.card (((F.H ⊓ d.fixedCentralizer u) ⊓ Lu).subgroupOf Lu) := by
  have hc : Nat.card (K F ⧸ pCore 2 (K F)) = 60 := by
    rw [Nat.card_congr d.KCoreAlternatingFive.toEquiv, nat_card_alternatingGroup,
      Nat.card_fin]
    decide
  have h5 : 5 ∣ Nat.card (K F) := by
    have hq := card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 (K F)))
      (QuotientGroup.mk'_surjective _)
    rw [hc] at hq
    exact dvd_trans (by decide : 5 ∣ 60) hq
  have hKM : K F ≤ (F.H ⊓ d.fixedCentralizer u) ⊓ Lu :=
    le_inf (le_inf (K_le_H F) (d.K_le_fixedCentralizer u h.member)) h.larger.le
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (show (F.H ⊓ d.fixedCentralizer u) ⊓ Lu ≤ Lu from inf_le_right)).toEquiv]
  exact h5.trans (card_dvd_of_le hKM)

/-- The index-fifteen alternative C.2.7(3)(c) cannot contain this K.
The argument uses the actual triple-cover order and a two-group core. -/
theorem fixedComponent_not_ahatSix (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) (hm : ChapterC.IsExceptionalAhat6Block Lu)
    (hi : (((F.H ⊓ d.fixedCentralizer u) ⊓ Lu).subgroupOf Lu).index = 15) : False := by
  let Q := Lu ⧸ pCore 2 Lu
  obtain ⟨e⟩ := hm.2.2.2.1
  have hq : Nat.card Q = 1080 := by
    have hc := (center Q).card_mul_index
    change Nat.card (center Q) * Nat.card (Q ⧸ center Q) = Nat.card Q at hc
    rw [hm.2.2.1, Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hc
    norm_num at hc
    exact hc.symm
  have hcore := (pCore 2 Lu).card_mul_index
  change Nat.card (pCore 2 Lu) * Nat.card Q = Nat.card Lu at hcore
  rw [hq] at hcore
  have h25 : 25 ∣ Nat.card Lu := by
    have hc := (((F.H ⊓ d.fixedCentralizer u) ⊓ Lu).subgroupOf Lu).card_mul_index
    rw [hi] at hc
    rw [← hc]
    exact (show 25 = 5 * 5 by decide) ▸
      Nat.mul_dvd_mul (d.fixedComponent_five_dvd_inter_card u h) (by decide : 5 ∣ 15)
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := Lu)).exists_card_dvd_pow
  have hd : 25 ∣ 2 ^ n * 1080 :=
    (h25.trans (hcore ▸ Nat.mul_dvd_mul_right hn 1080))
  have hcop : Nat.Coprime 25 (2 ^ n) := (by decide : Nat.Coprime 25 2).pow_right n
  have hbad : 25 ∣ 1080 := hcop.dvd_of_dvd_mul_left hd
  norm_num at hbad

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
