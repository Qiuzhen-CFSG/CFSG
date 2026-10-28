module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.SevenSylow
/-!
# Alternating-seven local components in even-characteristic carriers

The intrinsic Sylow action on A7 has order at most sixteen. Genuine triality,
Ree, and sporadic carriers except M11 have two-part at least thirty-two;
M11 is excluded by Lagrange's theorem. The Mathieu triple cover inherits
the faithful Sylow action from its actual odd-center quotient.
Source: the restricted A.3.12 list used in Aschbacher–Smith C.5.12, p.163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02.LocalModels ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

theorem not_seven_local_triality (T : Sylow 2 G) {B : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents T) [IsQuasisimple B]
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) (hmodel : IsAlternating B 7)
    {m : ℕ} (hm : 1 ≤ m) : ¬ Triality.Standard.IsTrialityGroupAt (2^m) G := by
  intro he
  have hE := (MainConverse.TrialityLocal.quasithin_and_evenCharacteristic_of_isTrialityGroupAt m hm he).2
  apply no_alternating_seven_local_of_even_large_twoPart T (hE T) hB hTB hmodel
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G m hm).mp he
  rw [Nat.card_congr e.toEquiv]
  have hd := (Triality.Standard.Parabolics.unipotent (Triality.Standard.binaryParameters m hm)).card_subgroup_dvd_card
  rw [Triality.Standard.Parabolics.card_unipotent_binary _ rfl] at hd
  have hd' : 2^(12*m) ∣ Nat.card (Triality.Standard.Carrier (Triality.Standard.binaryParameters m hm)) := by
    simpa only [Triality.Standard.binaryParameters_q,← pow_mul,Nat.mul_comm m 12] using hd
  exact (pow_dvd_pow 2 (by omega : 5 ≤ 12*m)).trans hd'

theorem not_seven_local_ree (T : Sylow 2 G) {B : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents T) [IsQuasisimple B]
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) (hmodel : IsAlternating B 7)
    {m : ℕ} (hm : 1 ≤ m) : ¬ IsReeF4At G m := by
  rintro ⟨d,⟨e⟩⟩
  let f := e.trans d.modelEquiv
  have hE := (MainConverse.ReeLocal.quasithin_evenCharacteristic_of_iso hm f).2
  apply no_alternating_seven_local_of_even_large_twoPart T (hE T) hB hTB hmodel
  rw [Nat.card_congr f.toEquiv]
  have hd : 2^(12*(2*m+1)) ∣ Nat.card (ReeF4.Model m) := by
    rw [← ReeF4.AutomorphismTwoRank.sylow_card m]
    exact (ReeF4.AutomorphismTwoRank.sylow m : Subgroup (ReeF4.Model m)).card_subgroup_dvd_card
  exact (pow_dvd_pow 2 (by omega : 5 ≤ 12*(2*m+1))).trans hd

private theorem sporadic_thirtytwo_dvd (name : ClassificationModels.SporadicName)
    (hne : name ≠ .j3) (hm : name ≠ .m11) : 32 ∣ Nat.card name.Carrier := by
  cases name with
  | m11 => exact (hm rfl).elim
  | m12 => change 32 ∣ Nat.card Sporadic.Mathieu.M12; rw [Sporadic.Mathieu.m12_order]; norm_num
  | m22 => change 32 ∣ Nat.card Sporadic.Mathieu.M22; rw [Sporadic.Mathieu.m22_order]; norm_num
  | m23 => change 32 ∣ Nat.card Sporadic.Mathieu.M23; rw [Sporadic.Mathieu.m23_order]; norm_num
  | m24 => change 32 ∣ Nat.card Sporadic.Mathieu.M24; rw [Sporadic.Mathieu.m24_order]; norm_num
  | j2 =>
      change 32 ∣ Nat.card Sporadic.LeechRelated.J2.Carrier
      rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]; norm_num
  | j3 => exact (hne rfl).elim
  | j4 => change 32 ∣ Nat.card Janko4.Model; rw [Janko4.Cardinality.Thompson.model_card]; norm_num
  | hs =>
      change 32 ∣ Nat.card Sporadic.LeechRelated.HS.Carrier
      rw [Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier]; norm_num
  | he => exact (by decide : 32 ∣ 2^10).trans Held.two_pow_ten_dvd_card
  | ru => change 32 ∣ Nat.card Rudvalis.Model; rw [Rudvalis.model_card]; norm_num

theorem not_seven_local_sporadic (T : Sylow 2 G) {B : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents T) [IsQuasisimple B]
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) (hmodel : IsAlternating B 7)
    (name : ClassificationModels.SporadicName) (hne : name ≠ .j3) :
    ¬ Nonempty (G ≃* name.Carrier) := by
  rintro ⟨e⟩
  by_cases hm : name = .m11
  · subst name
    have hd := B.card_subgroup_dvd_card
    rw [AlternatingSevenMaximal.card_of_model hmodel,Nat.card_congr e.toEquiv] at hd
    change 2520 ∣ Nat.card Sporadic.Mathieu.M11 at hd
    rw [Sporadic.Mathieu.m11_order] at hd
    norm_num at hd
  · apply no_alternating_seven_local_of_even_large_twoPart T (sporadic_evenCharacteristic name e T) hB hTB hmodel
    rw [Nat.card_congr e.toEquiv]
    exact sporadic_thirtytwo_dvd name hne hm

theorem not_seven_local_m22_cover (T : Sylow 2 G) {B : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents T) [IsQuasisimple B]
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) (hmodel : IsAlternating B 7) :
    ¬ IsM22Cover G := by
  intro hm
  have hf := sylow_faithful_of_m22_cover T hB hTB hm
  have ht := alternating_seven_normalizer_card_dvd T B hmodel hTB hf
  obtain ⟨_,⟨ec⟩,⟨eq⟩⟩ := hm
  have hc : Nat.card G=1330560 := by
    have h := (center G).card_mul_index
    rw [Nat.card_congr ec.toEquiv,index_eq_card,Nat.card_congr eq.toEquiv,Sporadic.Mathieu.m22_order] at h
    norm_num at h
    exact h.symm
  have hd : 32 ∣ Nat.card T := T.pow_dvd_card_of_pow_dvd_card (n := 5) (by rw [hc]; norm_num)
  have := hd.trans ht
  norm_num at this
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
