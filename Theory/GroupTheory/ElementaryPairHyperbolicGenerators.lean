module
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Hyperbolic generators for two elementary abelian subgroups

Let `C` and `D` be normal elementary abelian subgroups of order eight that
generate a finite group. If their intersection is the center and has order
two, then one can choose two involutions in each factor forming hyperbolic
commutator pairs: the paired commutators are the common central involution,
and all cross-pairings commute. These four involutions generate the group.

Normality places every mixed commutator in the common center. Choose a
noncentral `x1` in `C` and a noncommuting partner `y1` in `D`. Adjoining `x1`
to the center gives a subgroup of order four. An element outside it can be
multiplied by `x1` to give `x2` commuting with `y1`, still outside that
subgroup. A noncommuting partner of `x2` can likewise be multiplied by `y1`
to give `y2` commuting with `x1`. In either elementary subgroup, adjoining
these independent involutions doubles the order twice, proving generation.
The common central involution is itself the first paired commutator.

This is the elementary nondegenerate commutator-pairing argument underlying
the quaternion central-product recognition in Stellmacher (9.1), Journal of
Algebra 190 (1997), p.48. The statement is independent of the Stellmacher
campaign and supplies the inputs of `HyperbolicQuaternionFactors`.
-/

open scoped commutatorElement
open Subgroup
variable {G : Type*} [Group G]

private theorem elementary_commute (A : Subgroup G) [IsElementaryAbelian 2 A]
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) : Commute a b := by
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)

private theorem elementary_normalizes (A H : Subgroup G) [IsElementaryAbelian 2 A]
    (hHA : H ≤ A) {a : G} (ha : a ∈ A) : a ∈ normalizer (H : Set G) := by
  apply centralizer_le_normalizer _
  intro h hh
  exact (elementary_commute A (hHA hh) ha).eq

private theorem exists_noncommuting_partner (C D : Subgroup G)
    [IsElementaryAbelian 2 C] (hgen : C ⊔ D = ⊤)
    {x : G} (hxC : x ∈ C) (hxZ : x ∉ center G) :
    ∃ y ∈ D, ¬ Commute x y := by
  classical
  by_contra! hh
  apply hxZ
  apply mem_center_iff.mpr
  intro g
  have hle : C ⊔ D ≤ centralizer ({x} : Set G) := by
    apply sup_le
    · intro c hc
      exact mem_centralizer_singleton_iff.mpr (elementary_commute C hc hxC).eq
    · intro d hd
      exact mem_centralizer_singleton_iff.mpr (hh d hd).symm.eq
  exact mem_centralizer_singleton_iff.mp (hle (by rw [hgen]; trivial))

variable [Finite G]

public theorem exists_hyperbolic_involutions_of_elementary_pair
    (C D : Subgroup G) [IsElementaryAbelian 2 C] [IsElementaryAbelian 2 D]
    [C.Normal] [D.Normal] (hC : Nat.card C = 8) (hD : Nat.card D = 8)
    (hgen : C ⊔ D = ⊤) (hinter : C ⊓ D = center G)
    (hZ : Nat.card (center G) = 2) :
    ∃ x1 y1 x2 y2 z : G,
      x1 ∈ C ∧ y1 ∈ D ∧ x2 ∈ C ∧ y2 ∈ D ∧
      x1 ^ 2 = 1 ∧ y1 ^ 2 = 1 ∧ x2 ^ 2 = 1 ∧ y2 ^ 2 = 1 ∧
      z ≠ 1 ∧ z ^ 2 = 1 ∧ z ∈ center G ∧
      x1 * y1 * x1⁻¹ * y1⁻¹ = z ∧ x2 * y2 * x2⁻¹ * y2⁻¹ = z ∧
      Commute x1 x2 ∧ Commute x1 y2 ∧ Commute y1 x2 ∧ Commute y1 y2 ∧
      closure ({x1, y1, x2, y2} : Set G) = ⊤ := by
  classical
  have hZC : center G ≤ C := hinter ▸ inf_le_left
  have hZD : center G ≤ D := hinter ▸ inf_le_right
  obtain ⟨zz, hzz, hcases⟩ := (Nat.card_eq_two_iff' (1 : center G)).mp hZ
  let z : G := zz
  have hz : z ≠ 1 := fun hh => hzz (Subtype.ext hh)
  have hzc : z ∈ center G := zz.property
  have hz2 : z ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian z (hZC hzc)
  have hcase : ∀ t ∈ center G, t = 1 ∨ t = z := by
    intro t ht
    by_cases ht1 : t = 1
    · exact Or.inl ht1
    · exact Or.inr (congrArg Subtype.val (hcases ⟨t, ht⟩ (fun hh =>
        ht1 (congrArg Subtype.val hh))))
  have hbracket : ∀ c ∈ C, ∀ d ∈ D, ⁅c,d⁆ = 1 ∨ ⁅c,d⁆ = z := by
    intro c hc d hd
    apply hcase
    rw [← hinter]
    have hm := commutator_mem_commutator hc hd
    exact ⟨commutator_le_left C D hm, commutator_le_right C D hm⟩
  have hnoncomm : ∀ c ∈ C, ∀ d ∈ D, ¬ Commute c d → ⁅c,d⁆ = z := by
    intro c hc d hd hcd
    exact (hbracket c hc d hd).resolve_left (fun hh =>
      hcd (commutatorElement_eq_one_iff_mul_comm.mp hh))
  obtain ⟨x1, hx1C, hx1Z⟩ : ∃ x1 ∈ C, x1 ∉ center G := by
    by_contra! hh
    have hc := card_le_of_le hh
    rw [hC, hZ] at hc
    omega
  obtain ⟨y1, hy1D, hxy1n⟩ := exists_noncommuting_partner C D hgen hx1C hx1Z
  have hxy1 : ⁅x1,y1⁆ = z := hnoncomm x1 hx1C y1 hy1D hxy1n
  have hx12 := elemPow_eq_one_of_isElementaryAbelian (p := 2) x1 hx1C
  have hy12 := elemPow_eq_one_of_isElementaryAbelian (p := 2) y1 hy1D
  let H := center G ⊔ zpowers x1
  have hHC : H ≤ C := sup_le hZC (zpowers_le.mpr hx1C)
  have hx1H : x1 ∈ H := mem_sup_right (mem_zpowers x1)
  have hHcard : Nat.card H = 4 := by
    rw [card_sup_zpowers_of_normalizing_involution (center G) x1 hx12 hx1Z
      (elementary_normalizes C _ hZC hx1C), hZ]
  obtain ⟨t, htC, htH⟩ : ∃ t ∈ C, t ∉ H := by
    by_contra! hh
    have hc := card_le_of_le hh
    rw [hC, hHcard] at hc
    omega
  obtain ⟨x2, hx2C, hx2H, hx2y1⟩ : ∃ x2 ∈ C, x2 ∉ H ∧ Commute x2 y1 := by
    by_cases ht : Commute t y1
    · exact ⟨t, htC, htH, ht⟩
    · refine ⟨x1 * t, C.mul_mem hx1C htC, ?_, ?_⟩
      · intro hh
        exact htH ((H.mul_mem_cancel_left hx1H).mp hh)
      · apply commutatorElement_eq_one_iff_mul_comm.mp
        rw [commutatorElement_mul_left_eq_conj_mul, hnoncomm t htC y1 hy1D ht, hxy1,
          (mem_center_iff.mp hzc x1)]
        simpa only [mul_assoc, mul_inv_cancel_left, pow_two] using hz2
  have hx2Z : x2 ∉ center G := fun hh => hx2H (mem_sup_left hh)
  have hx22 := elemPow_eq_one_of_isElementaryAbelian (p := 2) x2 hx2C
  have hCgen : H ⊔ zpowers x2 = C := by
    apply eq_of_le_of_card_ge (sup_le hHC (zpowers_le.mpr hx2C))
    rw [card_sup_zpowers_of_normalizing_involution H x2 hx22 hx2H
      (elementary_normalizes C H hHC hx2C), hHcard, hC]
  obtain ⟨t2, ht2D, hx2t2⟩ := exists_noncommuting_partner C D hgen hx2C hx2Z
  have hx2t2z : ⁅x2,t2⁆ = z := hnoncomm x2 hx2C t2 ht2D hx2t2
  obtain ⟨y2, hy2D, hx1y2, hx2y2⟩ :
      ∃ y2 ∈ D, Commute x1 y2 ∧ ⁅x2,y2⁆ = z := by
    by_cases ht2 : Commute x1 t2
    · exact ⟨t2, ht2D, ht2, hx2t2z⟩
    · refine ⟨y1 * t2, D.mul_mem hy1D ht2D, ?_, ?_⟩
      · apply commutatorElement_eq_one_iff_mul_comm.mp
        rw [commutatorElement_mul_right_eq_mul_conj, hxy1,
          hnoncomm x1 hx1C t2 ht2D ht2,
          mul_assoc z y1, mem_center_iff.mp hzc y1]
        group
        simpa only [pow_two] using hz2
      · rw [commutatorElement_mul_right_eq_mul_conj,
          commutatorElement_eq_one_iff_mul_comm.mpr hx2y1.eq, hx2t2z, one_mul,
          mem_center_iff.mp hzc y1]
        group
  have hy22 := elemPow_eq_one_of_isElementaryAbelian (p := 2) y2 hy2D
  have hy1Z : y1 ∉ center G := by
    intro hh
    exact hxy1n (mem_center_iff.mp hh x1)
  let K := center G ⊔ zpowers y1
  have hKD : K ≤ D := sup_le hZD (zpowers_le.mpr hy1D)
  have hKcard : Nat.card K = 4 := by
    rw [card_sup_zpowers_of_normalizing_involution (center G) y1 hy12 hy1Z
      (elementary_normalizes D _ hZD hy1D), hZ]
  have hKcentral : K ≤ centralizer ({x2} : Set G) := by
    apply sup_le
    · intro v hv
      exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hv x2).symm
    · apply zpowers_le.mpr
      exact mem_centralizer_singleton_iff.mpr hx2y1.symm.eq
  have hy2K : y2 ∉ K := by
    intro hh
    have ht := commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_centralizer_singleton_iff.mp (hKcentral hh)).symm
    exact hz (hx2y2.symm.trans ht)
  have hDgen : K ⊔ zpowers y2 = D := by
    apply eq_of_le_of_card_ge (sup_le hKD (zpowers_le.mpr hy2D))
    rw [card_sup_zpowers_of_normalizing_involution K y2 hy22 hy2K
      (elementary_normalizes D K hKD hy2D), hKcard, hD]
  refine ⟨x1,y1,x2,y2,z,hx1C,hy1D,hx2C,hy2D,hx12,hy12,hx22,hy22,hz,hz2,hzc,
    hxy1,hx2y2,elementary_commute C hx1C hx2C,hx1y2,hx2y1.symm,
    elementary_commute D hy1D hy2D,?_⟩
  let S := closure ({x1,y1,x2,y2} : Set G)
  have hx1S : x1 ∈ S := subset_closure (by simp)
  have hy1S : y1 ∈ S := subset_closure (by simp)
  have hx2S : x2 ∈ S := subset_closure (by simp)
  have hy2S : y2 ∈ S := subset_closure (by simp)
  have hzS : z ∈ S := by
    rw [← hxy1, commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem hx1S hy1S) (S.inv_mem hx1S)) (S.inv_mem hy1S)
  have hZS : center G ≤ S := by
    intro v hv
    rcases hcase v hv with rfl | rfl
    · exact S.one_mem
    · exact hzS
  apply top_unique
  rw [← hgen]
  apply sup_le
  · rw [← hCgen]
    exact sup_le (sup_le hZS (zpowers_le.mpr hx1S)) (zpowers_le.mpr hx2S)
  · rw [← hDgen]
    exact sup_le (sup_le hZS (zpowers_le.mpr hy1S)) (zpowers_le.mpr hy2S)
