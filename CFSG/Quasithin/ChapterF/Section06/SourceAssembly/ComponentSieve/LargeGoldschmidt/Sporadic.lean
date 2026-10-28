module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.Sporadic
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
/-!
# The sporadic catalogue at Sylow orders thirty-two through 128

The actual carrier orders eliminate M11 and J1 below the lower bound and
M24, J4, HS, He and Ru above the upper bound. The four remaining carriers
are M12, M22, M23 and J2. At upper bound 64 only M12 remains; at exact
order 32 no sporadic carrier remains. Local subgroup order certificates
suffice for the two large carriers whose full orders are unnecessary.

This is the numeric part of Aschbacher–Smith F.6.18(10)–(13), printed p.310.
The marked amalgam must still distinguish the order-128 survivors.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.LargeGoldschmidt
open CFSG.Quasithin.ClassificationModels
open CFSG.Quasithin.ChapterA.Section02

private theorem large_sporadic_name_order (name : SporadicName) (hne : name ≠ .j3)
    (hn : name ≠ .m11 ∧ name ≠ .m12 ∧ name ≠ .m22 ∧ name ≠ .m23 ∧ name ≠ .j2) :
    256 ∣ Nat.card name.Carrier := by
  cases name with
  | m11 => exact (hn.1 rfl).elim
  | m12 => exact (hn.2.1 rfl).elim
  | m22 => exact (hn.2.2.1 rfl).elim
  | m23 => exact (hn.2.2.2.1 rfl).elim
  | m24 =>
      change 256 ∣ Nat.card Sporadic.Mathieu.M24
      rw [Sporadic.Mathieu.m24_order]
      norm_num
  | j2 => exact (hn.2.2.2.2 rfl).elim
  | j3 => exact (hne rfl).elim
  | j4 =>
      change 256 ∣ Nat.card Janko4.Model
      let hA := Janko4.matrixA_mul_self
      let hB := Janko4.matrixB_pow_four
      have hk := (Janko4.Cardinality.localKernel hA hB).card_subgroup_dvd_card
      rw [Janko4.Cardinality.localKernel_card hA hB] at hk
      exact (show 256 ∣ 2048 by norm_num).trans
        (hk.trans (Janko4.Cardinality.max1Subgroup hA hB).card_subgroup_dvd_card)
  | hs =>
      change 256 ∣ Nat.card Sporadic.LeechRelated.HS.Carrier
      rw [Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier]
      norm_num
  | he =>
      change 256 ∣ Nat.card Held.He
      let K : Subgroup Held.He := Subgroup.closure
        (Set.range Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair00Two.input)
      have hK : Nat.card K = 1024 :=
        Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrderCertificate.Factors.Pair00Two.order
      have hd := K.card_subgroup_dvd_card
      rw [hK] at hd
      exact (show 256 ∣ 1024 by norm_num).trans hd
  | ru =>
      change 256 ∣ Nat.card Rudvalis.Model
      rw [Rudvalis.model_card]
      norm_num

variable {G : Type*} [Group G] [Finite G]
private theorem not_256_dvd (P : Sylow 2 G) (hP : Nat.card P ≤ 128) :
    ¬ 256 ∣ Nat.card G := by
  intro hd
  have hh := Nat.le_of_dvd (Nat.card_pos (α := P))
    (P.pow_dvd_card_of_pow_dvd_card (n := 8) hd)
  norm_num at hh
  omega
private theorem thirty_two_dvd (P : Sylow 2 G) (hP : 32 ≤ Nat.card P) :
    32 ∣ Nat.card G := by
  obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
  have h5 : 5 ≤ n := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    exact hn ▸ hP
  have hd : 32 ∣ Nat.card P := by rw [hn]; exact pow_dvd_pow 2 h5
  exact hd.trans P.card_subgroup_dvd_card

theorem sporadic_of_sylow_between_thirty_two_and_128
    (P : Sylow 2 G) (hlo : 32 ≤ Nat.card P) (hhi : Nat.card P ≤ 128)
    (hm : IsTheoremCSporadicModel G) :
    Nonempty (G ≃* Sporadic.Mathieu.M12) ∨ Nonempty (G ≃* Sporadic.Mathieu.M22) ∨
      Nonempty (G ≃* Sporadic.Mathieu.M23) ∨ Nonempty (G ≃* Sporadic.LeechRelated.J2.Carrier) := by
  have h32 := thirty_two_dvd P hlo
  have h256 := not_256_dvd P hhi
  rcases hm with ⟨name,hne,⟨e⟩⟩ | hj
  · by_cases h11 : name = .m11
    · subst name
      rw [Nat.card_congr e.toEquiv] at h32
      change 32 ∣ Nat.card Sporadic.Mathieu.M11 at h32
      rw [Sporadic.Mathieu.m11_order] at h32
      norm_num at h32
    by_cases h12 : name = .m12
    · subst name; exact .inl ⟨e⟩
    by_cases h22 : name = .m22
    · subst name; exact .inr (.inl ⟨e⟩)
    by_cases h23 : name = .m23
    · subst name; exact .inr (.inr (.inl ⟨e⟩))
    by_cases hj2 : name = .j2
    · subst name; exact .inr (.inr (.inr ⟨e⟩))
    exact (h256 (Nat.card_congr e.toEquiv ▸
      large_sporadic_name_order name hne ⟨h11,h12,h22,h23,hj2⟩)).elim
  · obtain ⟨e⟩ := hj
    rw [Nat.card_congr e.toEquiv,Janko1.card_model] at h32
    norm_num at h32

theorem no_sporadic_of_sylow_thirty_two (P : Sylow 2 G) (hP : Nat.card P = 32) :
    ¬ IsTheoremCSporadicModel G := by
  intro hm
  have hn64 : ¬ 64 ∣ Nat.card G := by
    intro hd
    have hh := P.pow_dvd_card_of_pow_dvd_card (n := 6) hd
    rw [hP] at hh
    norm_num at hh
  rcases sporadic_of_sylow_between_thirty_two_and_128 P (by omega) (by omega) hm with
    he | he | he | he
  · obtain ⟨e⟩ := he
    apply hn64
    rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m12_order]
    norm_num
  · obtain ⟨e⟩ := he
    apply hn64
    rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m22_order]
    norm_num
  · obtain ⟨e⟩ := he
    apply hn64
    rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m23_order]
    norm_num
  · obtain ⟨e⟩ := he
    apply hn64
    rw [Nat.card_congr e.toEquiv,Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
    norm_num


theorem mathieu_twelve_of_sporadic_sylow_between_thirty_two_and_64
    (P : Sylow 2 G) (hlo : 32 ≤ Nat.card P) (hhi : Nat.card P ≤ 64)
    (hm : IsTheoremCSporadicModel G) : Nonempty (G ≃* Sporadic.Mathieu.M12) := by
  have hn128 : ¬ 128 ∣ Nat.card G := by
    intro hd
    have hh := Nat.le_of_dvd (Nat.card_pos (α := P))
      (P.pow_dvd_card_of_pow_dvd_card (n := 7) hd)
    norm_num at hh
    omega
  rcases sporadic_of_sylow_between_thirty_two_and_128 P hlo (by omega) hm with
    he | he | he | he
  · exact he
  · obtain ⟨e⟩ := he
    apply (hn128 _).elim
    rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m22_order]
    norm_num
  · obtain ⟨e⟩ := he
    apply (hn128 _).elim
    rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m23_order]
    norm_num
  · obtain ⟨e⟩ := he
    apply (hn128 _).elim
    rw [Nat.card_congr e.toEquiv,Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
    norm_num
end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.LargeGoldschmidt
