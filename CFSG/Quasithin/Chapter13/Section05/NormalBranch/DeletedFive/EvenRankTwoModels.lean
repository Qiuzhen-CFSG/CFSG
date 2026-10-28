module

public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.Cardinality
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.SymplecticFourModel
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import CFSG.Quasithin.ChapterC.Section03.A5.PSL3Four
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders
public import Theory.SpecificGroups.Tits.FiniteSimple
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The complete even rank-two inspection for the deleted-five branch

The actual block and its elementary layer force 960 to divide the ambient
order, whereas the source Sylow bound excludes a factor 512. Concrete
unipotent orders reduce the linear and symplectic families to PSL₃(4) and
Sp₄(4), respectively, and exclude G₂, triality, Ree and Tits. The two small
derived groups are excluded by their actual orders. The remaining linear
model contradicts the marked deleted-five action; the symplectic model
contradicts self-centralization of its order-sixteen elementary layer.

Source: Aschbacher–Smith 13.5.15, printed p.921, inspecting Theorem C,
A.2.4, printed p.33. All field and derived-carrier conventions are retained.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]

private theorem large_power_dvd {a b : ℕ} (h : 9 ≤ a * b) :
    512 ∣ (2 ^ a) ^ b := by
  rw [← pow_mul]
  exact Nat.pow_dvd_pow 2 h

omit [Finite G] in
private theorem linear_exponent_le_two {f : ℕ}
    (hsmall : ¬ 512 ∣ Nat.card G) (hm : ClassicalGroup.IsPSL G 3 (2 ^ f)) : f ≤ 2 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hd := (Matrix.PSL3.LinearThree.unipotent F).card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.card_unipotent, hF,
    ← Nat.card_congr e.toEquiv] at hd
  by_contra h
  exact hsmall ((large_power_dvd (by omega : 9 ≤ f * 3)).trans hd)

omit [Finite G] in
private theorem symplectic_exponent_le_two {f : ℕ}
    (hsmall : ¬ 512 ∣ Nat.card G) (hm : ClassicalGroup.IsPSp G 2 (2 ^ f)) : f ≤ 2 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  let a := e.trans (EvenProjective.equiv (F := F)).symm
  have hd := (unipotent (F := F)).card_subgroup_dvd_card
  rw [card_unipotent, hF, ← Nat.card_congr a.toEquiv] at hd
  by_contra h
  exact hsmall ((large_power_dvd (by omega : 9 ≤ f * 4)).trans hd)

omit [Finite G] in
private theorem not_g2_model {f : ℕ} (hf : 2 ≤ f)
    (hsmall : ¬ 512 ∣ Nat.card G) (hm : ClassificationModels.IsG2At G (2 ^ f)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  apply hsmall
  rw [Nat.card_congr e.toEquiv, Atlas.G2.card_Model, hF]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
    (large_power_dvd (by omega : 9 ≤ f * 6)) _) _

omit [Finite G] in
private theorem not_triality_model {f : ℕ} (hf : 1 ≤ f)
    (hsmall : ¬ 512 ∣ Nat.card G)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ f) G) : False := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G f (by omega)).mp hm
  let P := Triality.Standard.binaryParameters f (by omega : 0 < f)
  have hd := (Triality.Standard.Parabolics.unipotent P).card_subgroup_dvd_card
  rw [Triality.Standard.Parabolics.card_unipotent_binary P rfl] at hd
  change (2 ^ f) ^ 12 ∣ Nat.card (Triality.Standard.BinaryCarrier f _) at hd
  rw [← Nat.card_congr e.toEquiv] at hd
  exact hsmall ((large_power_dvd (by omega : 9 ≤ f * 12)).trans hd)

omit [Finite G] in
private theorem not_ree_model (m : ℕ) (hsmall : ¬ 512 ∣ Nat.card G)
    (e : G ≃* ReeF4.Model m) : False := by
  have hd := (ReeF4.Parabolics.unipotent m).card_subgroup_dvd_card
  rw [ReeF4.Parabolics.card_unipotent, ← Nat.card_congr e.toEquiv] at hd
  exact hsmall ((large_power_dvd (by omega : 9 ≤ (2 * m + 1) * 12)).trans hd)

private theorem not_linear_model {f : ℕ} (hf : 1 ≤ f)
    (hsmall : ¬ 512 ∣ Nat.card G) (hlarge : 960 ∣ Nat.card G)
    (K : Subgroup G) (hK : ChapterC.IsAlternatingBlock K 5)
    (hc : Nat.card ((ChapterC.blockU K).map K.subtype) = 16)
    (hm : ClassicalGroup.IsPSL G 3 (2 ^ f)) : False := by
  have hbound := linear_exponent_le_two hsmall hm
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  interval_cases f
  · have hcard : Nat.card G = 168 := by
      rw [Nat.card_congr e.toEquiv, Matrix.PSL3.LinearThree.card_projective, hF]
      norm_num
    rw [hcard] at hlarge
    norm_num at hlarge
  · let : Fintype F := Fintype.ofFinite F
    let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
    have hcard : Fintype.card F = Fintype.card Matrix.PSL3Four.F := by
      simpa only [← Nat.card_eq_fintype_card, Matrix.PSL3Four.card_F, Nat.reducePow] using hF
    let a := Atlas.fieldEquivPSL 3 (FiniteField.ringEquivOfCardEq hcard)
    exact ChapterC.no_alternatingFive_of_psl3Four_equiv (e.trans a) K hK hc

/-- None of the eight actual rank-two alternatives in Theorem C contains
this original self-centralizing deleted-five layer with the source Sylow bound. -/
theorem not_evenRankTwoModel
    (K : Subgroup G) (hK : ChapterC.IsAlternatingBlock K 5)
    (hc : Nat.card ((ChapterC.blockU K).map K.subtype) = 16)
    (hself : centralizer ((ChapterC.blockU K).map K.subtype : Set G) ≤
      (ChapterC.blockU K).map K.subtype)
    (T : Sylow 2 G) (hT : Nat.card T ≤ 256) {f : ℕ} :
    ¬ ChapterA.Section02.IsTheoremCRankTwoModel G f := by
  intro hm
  have hsmall := not_fiveHundredTwelve_dvd_of_sylow_bound T hT
  have hlarge := card_dvd_of_alternatingFive K hK hc
  cases hm with
  | linear hf hm => exact not_linear_model hf hsmall hlarge K hK hc hm
  | symplectic hf hm =>
    have hf2 : f = 2 := by have := symplectic_exponent_le_two hsmall hm; omega
    subst f
    let := hK.2.1.elementary
    let : IsElementaryAbelian 2 ((ChapterC.blockU K).map K.subtype) :=
      IsElementaryAbelian.map K.subtype
    exact not_symplecticFour_model _ hc hself (by simpa using hm)
  | g2 hf hm => exact not_g2_model hf hsmall hm
  | triality hf hm => exact not_triality_model hf hsmall hm
  | ree_f4 m _ _ hm => obtain ⟨e⟩ := hm; exact not_ree_model m hsmall e
  | symplectic_derived _ hm =>
    obtain ⟨e⟩ := hm
    have hcard : Nat.card G = 360 := by
      rw [Nat.card_congr (e.trans
        Binary.projectiveDerivedEquivAlternatingSix).toEquiv, nat_card_alternatingGroup]
      norm_num
    rw [hcard] at hlarge
    norm_num at hlarge
  | g2_derived _ hm =>
    obtain ⟨e⟩ := hm
    have hcard : Nat.card G = 6048 := by
      rw [Nat.card_congr e.toEquiv]
      exact Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)
    rw [hcard] at hlarge
    norm_num at hlarge
  | tits _ hm =>
    obtain ⟨e⟩ := hm
    apply hsmall
    rw [Nat.card_congr e.toEquiv, Tits.parrottGroup_card]
    norm_num

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
