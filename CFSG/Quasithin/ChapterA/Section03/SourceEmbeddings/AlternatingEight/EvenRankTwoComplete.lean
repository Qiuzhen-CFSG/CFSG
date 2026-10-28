module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.EvenRankTwo
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.EvenFaithfulSylow
public import CFSG.Quasithin.MainConverse.EvenLinearLocal
public import CFSG.Quasithin.MainConverse.EvenUnitarySymplecticLocal.ModelTransport
public import CFSG.Quasithin.MainConverse.ExceptionalLocal
public import CFSG.Quasithin.MainConverse.ReeLocal
public import Theory.SpecificGroups.BinaryLinear.SylowCenters
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders

/-!
# The full even rank-two exclusion for normalized local A₈ sections

When the intrinsic two-core vanishes, the smaller component is genuinely A₈.
Even characteristic makes its full-Sylow action faithful, so Aut(A₈) = S₈
forces the Sylow order to divide 128. The concrete unipotent orders exclude
every larger rank-two model. The remaining PSL₃(4) has Sylow center of order
four, whereas A₈ = PSL₄(2) has Sylow center of order at most two.
Combining this with the nontrivial-core branch removes the core premise.

Source: Aschbacher–Smith A.3.12 and 15.3.32(3), pp.47–48 and 1132.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
variable {G : Type*} [Group G] [Finite G]

private theorem linearThreeFour_separation {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) (e : PSL(3,F) ≃* PSL(4,ZMod 2)) : False := by
  let S := Matrix.PSL3.LinearThree.unipotentSylow F (n := 2) (by decide) (by simpa using hF)
  have hc : Nat.card (center S) = 4 := by
    change Nat.card (center (Matrix.PSL3.LinearThree.unipotent F)) = 4
    rw [← Nat.card_congr (centerCongr (Matrix.PSL3.LinearThree.unipotentEquiv F)).toEquiv]
    rw [← Matrix.PSL3Even.UnipotentGeometry.Z_eq_center,
      Matrix.PSL3Even.UnipotentGeometry.card_Z,hF]
  have hb := BinaryLinear.psl_sylow_center_card_le_two (by decide : 2 ≤ 4)
    (S.mapSurjective (f := e.toMonoidHom) e.surjective)
  rw [← BinaryLinear.sylow_center_card_congr e S,hc] at hb
  omega

private theorem large_power_dvd {a b : ℕ} (h : 8 ≤ a * b) : 256 ∣ (2 ^ a) ^ b := by
  rw [← pow_mul]
  exact Nat.pow_dvd_pow 2 h

private theorem not_linear_of_small_twoPart
    {B : Subgroup G} (hA : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (hcore : pCore 2 B = ⊥) (hsmall : ¬ 256 ∣ Nat.card G)
    {n : ℕ} (hn : 1 ≤ n) (hm : ClassicalGroup.IsPSL G 3 (2 ^ n)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hn2 : n ≤ 2 := by
    have hd := (Matrix.PSL3.LinearThree.unipotent F).card_subgroup_dvd_card
    rw [Matrix.PSL3.LinearThree.card_unipotent,hF,← Nat.card_congr e.toEquiv] at hd
    by_contra h
    exact hsmall ((large_power_dvd (by omega : 8 ≤ n * 3)).trans hd)
  interval_cases n
  · have hd := ambient_card_dvd hA
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF] at hd
    norm_num at hd
  · let q : B ⧸ pCore 2 B ≃* B :=
      (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
    have hcardB : Nat.card B = 20160 :=
      (Nat.card_congr q.toEquiv).symm.trans (quotient_card hA)
    have hcardG : Nat.card G = 20160 := by
      rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF]
      norm_num
    have ht : B = ⊤ := B.eq_top_of_card_eq (hcardB.trans hcardG.symm)
    let t : G ≃* B := ((MulEquiv.subgroupCongr ht).trans topEquiv).symm
    obtain ⟨a⟩ := quotient_equiv hA
    let k := e.symm.trans (t.trans (q.symm.trans
      (a.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two)))
    exact linearThreeFour_separation (by simpa using hF) k

omit [Finite G] in
private theorem not_symplectic_of_small_twoPart
    (hsmall : ¬ 256 ∣ Nat.card G) {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSp G 2 (2 ^ n)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
  have hd := (Theory.SpecificGroups.SymplecticFour.unipotent (F := F)).card_subgroup_dvd_card
  rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,hF,
    ← Nat.card_congr a.toEquiv] at hd
  exact hsmall ((large_power_dvd (by omega : 8 ≤ n * 4)).trans hd)

omit [Finite G] in
private theorem not_g2_of_small_twoPart
    (hsmall : ¬ 256 ∣ Nat.card G) {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassificationModels.IsG2At G (2 ^ n)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  apply hsmall
  rw [Nat.card_congr e.toEquiv,Atlas.G2.card_Model,hF]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
    (large_power_dvd (by omega : 8 ≤ n * 6)) _) _

omit [Finite G] in
private theorem not_triality_of_small_twoPart
    (hsmall : ¬ 256 ∣ Nat.card G) {n : ℕ} (hn : 1 ≤ n)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) G) : False := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G n (by omega)).mp hm
  let P := Triality.Standard.binaryParameters n (by omega : 0 < n)
  have hd := (Triality.Standard.Parabolics.unipotent P).card_subgroup_dvd_card
  rw [Triality.Standard.Parabolics.card_unipotent_binary P rfl] at hd
  change (2 ^ n) ^ 12 ∣ Nat.card (Triality.Standard.BinaryCarrier n _) at hd
  rw [← Nat.card_congr e.toEquiv] at hd
  exact hsmall ((large_power_dvd (by omega : 8 ≤ n * 12)).trans hd)

omit [Finite G] in
private theorem not_ree_of_small_twoPart (m : ℕ) (hsmall : ¬ 256 ∣ Nat.card G)
    (e : G ≃* ReeF4.Model m) : False := by
  have hd := (ReeF4.Parabolics.unipotent m).card_subgroup_dvd_card
  rw [ReeF4.Parabolics.card_unipotent,← Nat.card_congr e.toEquiv] at hd
  exact hsmall ((large_power_dvd (by omega : 8 ≤ (2 * m + 1) * 12)).trans hd)

/-- The literal normalized local A₈ section excludes every Theorem C rank-two
model. The original subgroup is allowed a nontrivial two-core. -/
theorem not_rankTwo [IsSimpleGroup G]
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hA : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    {n : ℕ} (hm : ChapterA.Section02.IsTheoremCRankTwoModel G n) : False := by
  by_cases hcore : pCore 2 B = ⊥
  · have hs (hE : IsEvenCharacteristic G) : ¬ 256 ∣ Nat.card G :=
      not_twoPower_dvd_of_core_eq_bot S (hE S) hB hSB hA hcore
    cases hm with
    | linear hn hm =>
      exact not_linear_of_small_twoPart hA hcore
        (hs (MainConverse.psl3_two_pow_quasithin_and_evenCharacteristic hn hm).2) hn hm
    | symplectic hn hm =>
      exact not_symplectic_of_small_twoPart
        (hs (MainConverse.psp4_two_pow_quasithin_and_evenCharacteristic hn hm).2) hn hm
    | g2 hn hm =>
      exact not_g2_of_small_twoPart
        (hs (MainConverse.ExceptionalLocal.g2_even_quasithin_evenCharacteristic hn hm).2) hn hm
    | triality hn hm =>
      exact not_triality_of_small_twoPart
        (hs (MainConverse.ExceptionalLocal.triality_even_quasithin_evenCharacteristic hn hm).2) hn hm
    | ree_f4 m hm _ he =>
      exact not_ree_of_small_twoPart m
        (hs (MainConverse.ReeLocal.quasithin_evenCharacteristic_of_iso hm he.some).2) he.some
    | symplectic_derived _ he =>
      have hd := ambient_card_dvd hA
      rw [Nat.card_congr (he.some.trans
        Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).toEquiv,
        nat_card_alternatingGroup] at hd
      norm_num at hd
    | g2_derived _ he =>
      have hd := ambient_card_dvd hA
      rw [Nat.card_congr he.some.toEquiv,
        Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
      norm_num at hd
    | tits _ he =>
      have hd := ambient_card_dvd hA
      rw [Nat.card_congr he.some.toEquiv,Tits.parrottGroup_card] at hd
      norm_num at hd
  · exact not_rankTwo_of_core_ne_bot S hB hA hcore hm

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
