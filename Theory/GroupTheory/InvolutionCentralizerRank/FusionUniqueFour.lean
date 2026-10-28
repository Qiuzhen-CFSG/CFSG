module
public import Theory.GroupTheory.PGroup.NormalFourInvolutionFusion
public import Theory.GroupTheory.WeaklyClosedInvolutionSimple
public import Theory.GroupTheory.NormalFourFusion
public import Theory.GroupTheory.PGroup.RankTwoNormalFourTransfer
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Global involution fusion from a unique normal four

Let a finite simple group have a Sylow two-subgroup of elementary rank two,
a central omega subgroup of order two, and a unique normal elementary four.
Transfer moves every involution into the four. If the central involution had
no distinct conjugate there, the unique-four weak-closure theorem would make it
central in the simple group. Thus one conjugacy in the four fuses all its
nonidentity elements, and every ambient involution class is the same.

The local transfer helper retains the literal Sylow rank bound required by the
source. This is the unique-normal-four branch of GLS4, Chapter 1, Lemma 4.10,
`refs/KGroup/GLS4/Chapter1.tex`, lines 588--606.
-/

open Subgroup

namespace Sylow

/-- Local-rank form of transfer into a normal four-group. -/
public theorem exists_isConj_mem_normal_four_of_sylow_rank
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (hrank : ∀ A : Subgroup S, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) (t : S) (ht : orderOf t = 2) :
    ∃ u : S, u ∈ E ∧ IsConj (t : G) (u : G) := by
  have hindex := centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
    S.isPGroup' hZ E hE
  obtain ⟨u, htu, hu⟩ := S.exists_isConj_mem_of_index_two hno
    (centralizer (E : Set S)) hindex t ht
  have ht2 : (t : G) ^ 2 = 1 :=
    congrArg Subtype.val (show t ^ 2 = 1 by simpa only [ht] using pow_orderOf_eq_one t)
  have hu2 : u ^ 2 = 1 := by
    apply Subtype.ext
    have h := htu.pow 2
    rw [ht2] at h
    exact isConj_one_right.mp h
  exact ⟨u, mem_four_of_square_eq_one_of_elementary_card_lt_eight
    hrank E hE hu2 hu, htu⟩

/-- The unique-normal-four case of rank-two involution fusion. -/
public theorem isConj_involutions_of_unique_normal_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hcenter : center G = ⊥)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (hrank : ∀ A : Subgroup S, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  classical
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  let z : S := z₀.val.val
  have hz : orderOf z = 2 :=
    (orderOf_coe z₀.val).trans ((orderOf_coe z₀).trans hz₀)
  have hzC : z ∈ center S := z₀.val.property
  have hz1 : z ≠ 1 := (orderOf_eq_prime_iff.mp hz).2
  have hzE : z ∈ E := mem_four_of_square_eq_one_of_elementary_card_lt_eight
    hrank E hE (by simpa only [hz] using pow_orderOf_eq_one z)
      (center_le_centralizer _ hzC)
  have hnotweak : ¬ (∀ t : S, t ∈ E → IsConj (z : G) (t : G) → t = z) := by
    intro hweak
    have hzG := S.weakly_closed_involution_mem_center_of_simple z hz hzC
      (S.eq_of_isConj_of_weakly_closed_in_unique_normal_four_of_sylow_rank
        hrank E hE hunique z hzC hz hweak)
    have hzone : z = 1 := Subtype.ext (by simpa only [hcenter, mem_bot, coe_one] using hzG)
    exact hz1 hzone
  push Not at hnotweak
  obtain ⟨u, huE, hzu, huz⟩ := hnotweak
  have hu1 : u ≠ 1 := by
    intro hu
    have hzg : (z : G) = 1 := isConj_one_left.mp (by simpa only [hu, coe_one] using hzu)
    exact hz1 (Subtype.ext hzg)
  have hfusion := normal_four_fusion_of_central_isConj E hE
    (four_not_le_center_of_card_omega_one_center_eq_two hZ E hE)
    (⟨z, hzE⟩ : E) hzC (fun he => hz1 (congrArg Subtype.val he))
    (S : Subgroup G).subtype (⟨u, huE⟩ : E)
    (fun he => hu1 (congrArg Subtype.val he))
    (fun he => huz (congrArg Subtype.val he)) hzu
  have hcoverage (a : G) (ha : orderOf a = 2) :
      ∃ v : E, v ≠ 1 ∧ IsConj a ((v : S) : G) := by
    obtain ⟨t, hat⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using ha)
    obtain ⟨g, hg⟩ := isConj_iff.mp hat
    change (MulAut.conj g) a = (t : G) at hg
    have ht : orderOf t = 2 := by
      rw [← orderOf_coe, ← hg, MulEquiv.orderOf_eq, ha]
    obtain ⟨v, hvE, htv⟩ :=
      S.exists_isConj_mem_normal_four_of_sylow_rank hno hrank hZ E hE t ht
    have hav := hat.trans htv
    refine ⟨⟨v, hvE⟩, ?_, hav⟩
    intro he
    have hv1 : v = 1 := congrArg Subtype.val he
    have ha1 : a = 1 := isConj_one_left.mp (by simpa only [hv1, coe_one] using hav)
    simp [ha1] at ha
  obtain ⟨v, hv, hxv⟩ := hcoverage x hx
  obtain ⟨w, hw, hyw⟩ := hcoverage y hy
  exact hxv.trans ((hfusion v w hv hw).trans hyw.symm)

end Sylow
