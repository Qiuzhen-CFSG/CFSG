module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveFaithfulSylow
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFive
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.SpecificGroups.SymplecticFour.Sylow.FlagCounts
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import CFSG.Quasithin.MainConverse.EvenLinearLocal
public import CFSG.Quasithin.MainConverse.EvenUnitarySymplecticLocal.ModelTransport
public import CFSG.Quasithin.MainConverse.ExceptionalLocal
public import CFSG.Quasithin.MainConverse.ReeLocal
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock

/-!
# Rank-two containing models for a local A₅

The full Sylow normalizes the actual smaller A₅. Even characteristic makes
its action faithful, bounding its order by eight. The unipotent subgroups
exclude every large characteristic-two rank-two model; the small PSL₃(2)
and G₂(2)' endpoints have no factor five, and the Sp₄(2)' endpoint is A₆,
whose proper full-Sylow overgroups are solvable.

Source: Aschbacher--Smith A.3.14 and 10.2.1, printed pp.49--50 and743.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFive
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem ambient_card_dvd {B : Subgroup G}
    (e : B ≃* alternatingGroup (Fin 5)) : 60 ∣ Nat.card G := by
  have h := B.card_subgroup_dvd_card
  rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at h
  norm_num at h ⊢
  exact h

private theorem power_dvd {a b : ℕ} (h : 4 ≤ a * b) : 16 ∣ (2 ^ a) ^ b := by
  rw [← pow_mul]
  exact Nat.pow_dvd_pow 2 h

omit [Finite G] in
private theorem not_linear_of_small_twoPart {B : Subgroup G}
    (eB : B ≃* alternatingGroup (Fin 5)) (hsmall : ¬ 16 ∣ Nat.card G)
    {n : ℕ} (hn : 1 ≤ n) (hm : ClassicalGroup.IsPSL G 3 (2 ^ n)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  by_cases hn2 : 2 ≤ n
  · have hd := (Matrix.PSL3.LinearThree.unipotent F).card_subgroup_dvd_card
    rw [Matrix.PSL3.LinearThree.card_unipotent,hF,← Nat.card_congr e.toEquiv] at hd
    exact hsmall ((power_dvd (by omega : 4 ≤ n * 3)).trans hd)
  · have hn1 : n = 1 := by omega
    have hd := ambient_card_dvd eB
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF,hn1] at hd
    norm_num at hd

omit [Finite G] in
private theorem not_symplectic_of_small_twoPart
    (hsmall : ¬ 16 ∣ Nat.card G) {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSp G 2 (2 ^ n)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
  have hd := (Theory.SpecificGroups.SymplecticFour.unipotent (F := F)).card_subgroup_dvd_card
  rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,hF,
    ← Nat.card_congr a.toEquiv] at hd
  exact hsmall ((power_dvd (by omega : 4 ≤ n * 4)).trans hd)

omit [Finite G] in
private theorem not_g2_of_small_twoPart
    (hsmall : ¬ 16 ∣ Nat.card G) {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassificationModels.IsG2At G (2 ^ n)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  apply hsmall
  rw [Nat.card_congr e.toEquiv,Atlas.G2.card_Model,hF]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
    (power_dvd (by omega : 4 ≤ n * 6)) _) _

omit [Finite G] in
private theorem not_triality_of_small_twoPart
    (hsmall : ¬ 16 ∣ Nat.card G) {n : ℕ} (hn : 1 ≤ n)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) G) : False := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G n (by omega)).mp hm
  let P := Triality.Standard.binaryParameters n (by omega : 0 < n)
  have hd := (Triality.Standard.Parabolics.unipotent P).card_subgroup_dvd_card
  rw [Triality.Standard.Parabolics.card_unipotent_binary P rfl] at hd
  change (2 ^ n) ^ 12 ∣ Nat.card (Triality.Standard.BinaryCarrier n _) at hd
  rw [← Nat.card_congr e.toEquiv] at hd
  exact hsmall ((power_dvd (by omega : 4 ≤ n * 12)).trans hd)

omit [Finite G] in
private theorem not_ree_of_small_twoPart (m : ℕ) (hsmall : ¬ 16 ∣ Nat.card G)
    (e : G ≃* ReeF4.Model m) : False := by
  have hd := (ReeF4.Parabolics.unipotent m).card_subgroup_dvd_card
  rw [ReeF4.Parabolics.card_unipotent,← Nat.card_congr e.toEquiv] at hd
  exact hsmall ((power_dvd (by omega : 4 ≤ (2 * m + 1) * 12)).trans hd)

/-- A full-Sylow local A₅ cannot lie in A₆, including transported carriers. -/
theorem not_six (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (eB : B ≃* alternatingGroup (Fin 5)) (e : G ≃* alternatingGroup (Fin 6)) : False := by
  let f := e.toMonoidHom
  let : Group.IsSolvable f.ker := by
    rw [show f.ker = ⊥ from (MonoidHom.ker_eq_bot_iff _).mpr e.injective]
    infer_instance
  exact alternatingSix_not_local_five (B.map f)
    ((B.equivMapOfInjective f e.injective).symm.trans eB)
    (S.mapSurjective e.surjective)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hB f)

/-- Every literal Theorem C characteristic-two rank-two row is excluded. -/
theorem not_rankTwo (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (eB : B ≃* alternatingGroup (Fin 5))
    (hm : Chapter1.Section02.LocalModels.RankTwoTheoremC G) : False := by
  have hs (hE : IsEvenCharacteristic G) : ¬ 16 ∣ Nat.card G :=
    not_sixteen_dvd_of_evenCharacteristic S (hE S) hB hSB eB
  cases hm with
  | linear n hn hm =>
    exact not_linear_of_small_twoPart eB
      (hs (MainConverse.psl3_two_pow_quasithin_and_evenCharacteristic hn hm).2) hn hm
  | symplectic n hn hm =>
    exact not_symplectic_of_small_twoPart
      (hs (MainConverse.psp4_two_pow_quasithin_and_evenCharacteristic hn hm).2) hn hm
  | g2 n hn hm =>
    exact not_g2_of_small_twoPart
      (hs (MainConverse.ExceptionalLocal.g2_even_quasithin_evenCharacteristic hn hm).2) hn hm
  | triality n hn hm =>
    exact not_triality_of_small_twoPart
      (hs (MainConverse.ExceptionalLocal.triality_even_quasithin_evenCharacteristic hn hm).2) hn hm
  | ree m hm he =>
    obtain ⟨e⟩ := (ReeF4.exists_localBlockInput_mulEquiv_iff G m).mp he
    exact not_ree_of_small_twoPart m
      (hs (MainConverse.ReeLocal.quasithin_evenCharacteristic_of_iso hm e).2) e
  | symplectic_derived he =>
    exact not_six S hB eB (he.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
  | g2_derived he =>
    have hd := ambient_card_dvd eB
    rw [Nat.card_congr he.some.toEquiv,
      Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
    norm_num at hd
  | tits he =>
    apply hs (MainConverse.ExceptionalLocal.tits_model_evenCharacteristic he.some)
    rw [Nat.card_congr he.some.toEquiv,Tits.parrottGroup_card]
    decide

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFive
