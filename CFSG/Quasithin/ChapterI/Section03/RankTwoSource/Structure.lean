module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Structure
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits
public import CFSG.Quasithin.ChapterA.Section02.OddPrimeRank
public import Theory.GroupTheory.CComponent.TwoComponent
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankZero
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.GeneralizedFitting.NilpotentComponentPreimage
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.LinearRank
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSylows.Linear
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The rank-two deduction from the full A.3.6 alternatives

The natural and nilpotent alternatives have a kernel of order prime to
three and quotient SL₂ over an odd prime field. Their three-rank is at
most one. A C-component of three-rank two is therefore an ordinary
component in the two-core quotient. For a two-component the two-core is
central, so quasisimplicity lifts to the original group.

The full A.3.6 implication remains the genuine earlier-source input owned
by `qt-a03-sqtk-structure`; none of its cases is omitted.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterI.RankTwoSource
open Chapter1.Section02 Chapter1.Section02.LocalModels
universe u

/-- The existing complete A.3.6 contract, at its stated two-core-free boundary. -/
def EarlierA36 (κ : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X], IsSQTK κ X → pCore 2 X = ⊥ →
    ∀ K : Subgroup X, K.IsCComponent → A36Conclusion K

/-- The full source orbit/model alternative of A.3.8(3). -/
def EarlierA38 (κ : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X], IsSQTK κ X → pCore 2 X = ⊥ →
    ∀ K : Subgroup X, K.IsCComponent →
      K.Normal ∨ (normalizer (K : Set X)).index = 2 ∧ NonnormalCComponentModel K

private theorem three_rank_sl2_prime {F : Type} [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hc : Nat.card F = p) :
    primeRank 3 SL(2,F) ≤ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hc)
  rw [primeRank_equiv 3 (Atlas.fieldEquivSL 2 eF)]
  let P : Sylow 3 SL(2,ZMod p) := default
  exact P.primeRank_le_one_of_isCyclic
    (Matrix.SU3.InnerThreeRank.sl2_sylow_three_isCyclic p ho P)

private theorem three_rank_isSL_prime {K : Type u} [Group K] [Finite K]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : IsSL K 2 p) :
    primeRank 3 K ≤ 1 := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hm
  rw [primeRank_equiv 3 e]
  exact three_rank_sl2_prime hp ho hc

private theorem three_rank_of_kernel {K : Type u} [Group K] [Finite K]
    (N : Subgroup K) [N.Normal] (hn : ¬ 3 ∣ Nat.card N)
    (hr : primeRank 3 (K ⧸ N) ≤ 1) : primeRank 3 K ≤ 1 := by
  have hz : primeRank 3 N = 0 := PrimeRank.eq_zero_iff_not_dvd_card.mpr hn
  have h := primeRank_le_ker_add (p := 3) (QuotientGroup.mk' N)
  rw [QuotientGroup.ker_mk', hz, zero_add] at h
  exact h.trans hr

theorem a36Natural_three_rank_le_one {K : Type u} [Group K] [Finite K]
    (h : A36Natural K) : primeRank 3 K ≤ 1 := by
  obtain ⟨p, hp, hlarge, F, hF, hfin, hc, v, ρ, _⟩ := h.2
  have hcard : Nat.card (generalizedFitting K) = p ^ 2 := by
    rw [Nat.card_congr v.toEquiv]
    change Nat.card (Fin 2 → F) = p ^ 2
    rw [Nat.card_fun, Nat.card_fin, hc]
  apply three_rank_of_kernel (generalizedFitting K)
  · rw [hcard]
    intro hd
    have hp3 := Nat.prime_three.dvd_of_dvd_pow hd
    have he := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hp3
    omega
  · rw [primeRank_equiv 3 ρ]
    exact three_rank_sl2_prime hp (hp.odd_of_ne_two (by omega)) hc

theorem a36Nilpotent_three_rank_le_one {K : Type u} [Group K] [Finite K]
    (h : A36Nilpotent K) : primeRank 3 K ≤ 1 := by
  apply three_rank_of_kernel (generalizedFitting K)
  · intro hd
    have hc := (h.2.2.2 3 (by decide) hd).1
    norm_num at hc
  · exact three_rank_isSL_prime (by decide : Nat.Prime 5) (by decide) h.2.2.1

/-- No ordinary-component conclusion is assumed: it is obtained by eliminating
the two nonquasisimple alternatives in the complete source classification. -/
theorem component_of_A36_rank_two {X : Type u} [Group X] [Finite X]
    {L : Subgroup X} (h : A36Conclusion L) (hr : 2 ≤ primeRank 3 L) :
    IsComponent X L := by
  cases h.1 with
  | simple hc _ _ => exact hc
  | cover hc _ _ => exact hc
  | natural hn => have hb := a36Natural_three_rank_le_one hn; omega
  | nilpotent hn => have hb := a36Nilpotent_three_rank_le_one hn; omega

theorem sqtk_twoCore_quotient {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} (h : IsSQTK κ G) : IsSQTK κ (G ⧸ pCore 2 G) := by
  refine ⟨?_, h.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (h.stronglyQuasithin p hp ho)

theorem three_rank_twoCore_quotient {G : Type u} [Group G] [Finite G] :
    primeRank 3 (G ⧸ pCore 2 G) = primeRank 3 G := by
  apply le_antisymm
  · exact primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup
  · have hz : primeRank 3 (pCore 2 G) = 0 := by
      apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
      intro hd
      obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
      rw [hn] at hd
      have hh := Nat.prime_three.dvd_of_dvd_pow hd
      norm_num at hh
    have h := primeRank_le_ker_add (p := 3) (QuotientGroup.mk' (pCore 2 G))
    rw [QuotientGroup.ker_mk'] at h
    rw [hz, zero_add] at h
    exact h

/-- The odd-core quotient in the definition of a two-component makes its
two-core central; this is the actual kernel used in the lift below. -/
theorem twoComponent_twoCore_central {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} (hL : L.IsTwoComponent) : pCore 2 L ≤ center L := by
  let := hL.2
  apply twoCore_central_of_odd_kernel (QuotientGroup.mk' (pPrimeCore 2 L))
    (QuotientGroup.mk'_surjective _)
  rw [QuotientGroup.ker_mk']
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

/-- The local quasisimplicity deduction needed in I.3.1(3), with the full
A.3.6 implication explicit and no B₂ input. -/
theorem twoComponent_quasisimple_of_rank_two
    {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
    (hA36 : EarlierA36 κ) (hG : IsSQTK κ G)
    {L : Subgroup G} (hL : L.IsTwoComponent) (hr : 2 ≤ primeRank 3 L) :
    IsQuasisimple L := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let C := L.map q
  have hC := proposition_1_2_1_four_earlier_conclusion hA36 (sqtk_twoCore_quotient hG) hL.1
  let e : (L ⧸ pCore 2 L) ≃* C := cComponentTwoCoreQuotientEquiv hL.1
  have hrC : 2 ≤ primeRank 3 C := by
    rw [← primeRank_equiv 3 e, three_rank_twoCore_quotient]
    exact hr
  have hc := component_of_A36_rank_two hC hrC
  let : IsQuasisimple C := hc.2
  let : IsQuasisimple (L ⧸ pCore 2 L) := IsQuasisimple.of_mulEquiv e.symm
  let f : PerfectCentralCovering.Cover L (L ⧸ pCore 2 L) := {
    toMonoidHom := QuotientGroup.mk' (pCore 2 L)
    surjective := QuotientGroup.mk'_surjective _
    isPerfect := hL.1.perfect
    ker_le_center := by
      rw [QuotientGroup.ker_mk']
      exact twoComponent_twoCore_central hL }
  exact f.isQuasisimple

private theorem three_rank_le_one_of_square_not_dvd {G : Type u}
    [Group G] [Finite G] (h : ¬ 3 ^ 2 ∣ Nat.card G) : primeRank 3 G ≤ 1 := by
  apply (primeRank_le_iff_elementary_card_le G).mpr
  intro E hE
  let := hE
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 3 E).exists_card_eq
  have hd := E.card_subgroup_dvd_card
  rw [hn] at hd
  have hn1 : n ≤ 1 := by
    by_contra hh
    exact h ((pow_dvd_pow 3 (by omega : 2 ≤ n)).trans hd)
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) hn1

/-- Each of the actual four nonnormal models has three-rank at most one. -/
theorem nonnormalCComponentModel_three_rank_le_one {G : Type u}
    [Group G] [Finite G] (h : NonnormalCComponentModel G) : primeRank 3 G ≤ 1 := by
  cases h with
  | linear_even n hn hm =>
      obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hm
      let : Fintype F := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
        (by simpa only [← Nat.card_eq_fintype_card] using hc)
      rw [primeRank_equiv 3 e]
      let S : Sylow 3 SL(2,F) := default
      exact S.primeRank_le_one_of_surjective
        (Matrix.SL2.odd_pGroup_isCyclic_of_injective S.isPGroup' (by decide)
          (S : Subgroup SL(2,F)).subtype (S : Subgroup SL(2,F)).subtype_injective)
        (QuotientGroup.mk' (center SL(2,F))) (QuotientGroup.mk'_surjective _)
  | linear_prime p hp ho hm =>
      obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hm
      rw [primeRank_equiv 3 e]
      exact (PrimeRank.le_of_surjective_of_source_le_one (by decide : 3 ≠ 2)
        (QuotientGroup.mk' (center SL(2,F))) (QuotientGroup.mk'_surjective _)
        (three_rank_sl2_prime hp ho hc)).trans (three_rank_sl2_prime hp ho hc)
  | suzuki m hm he =>
      obtain ⟨e⟩ := he
      rw [primeRank_equiv 3 e]
      have hz : primeRank 3 (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) = 0 :=
        PrimeRank.eq_zero_iff_not_dvd_card.mpr
          (BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega))
      omega
  | janko he =>
      obtain ⟨e⟩ := he
      rw [primeRank_equiv 3 e]
      apply three_rank_le_one_of_square_not_dvd
      rw [Janko1.card_model]
      norm_num

/-- A.3.8's exceptional models are excluded by the actual rank, after the
proved transport through the two-core quotient. -/
theorem cComponent_normal_of_rank_two {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} (hA38 : EarlierA38 κ) (hG : IsSQTK κ G)
    {L : Subgroup G} (hL : L.IsCComponent) (hr : 2 ≤ primeRank 3 L) : L.Normal := by
  rcases proposition_1_2_1_three_index_of_A_3_8 hA38 (sqtk_twoCore_quotient hG) hL with
    hn | ⟨_, hm⟩
  · exact hn
  · have hb := nonnormalCComponentModel_three_rank_le_one hm
    rw [three_rank_twoCore_quotient] at hb
    omega

end CFSG.Quasithin.ChapterI.RankTwoSource
