module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.LocalStructure
public import Theory.GroupTheory.GeneralizedFitting.ElementaryEightNormal
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.PPrimeCore
public import Mathlib.Data.Fintype.Perm

/-!
# Normal structure and movement of the two G₂(3)-type subgroups

The actual PSL₃(2) quotient and full action on the elementary eight make M
perfect and centerless, with normal subgroups exactly 1, V, and M. This
classifies the intersections of ambient normal subgroups with the literal M.
It also kills every M-action on a group of order prime to seven.

The two commuting SL₂(3) factors bound |Z(H)| by four: multiply first by
one factor, then the other, using their centers of order two and |H| = 576.
If M normalized H, its action on Z(H) would be trivial, since 7 does not
divide 4!. But Z(H) contains the distinguished involution whose ambient
centralizer is H, forcing M ≤ H, contrary to the local orders. Thus M does
not normalize H; in particular H is not ambient normal. A normal subgroup
supplemented by H must contain M, by the factor seven in every proper normal
index of M. Thus the odd core cannot supplement H. This discharges the
nondegeneracy premise G ≠ C_G(z)O(G) of Fong–Wong §2F.

These are ambient consequences of (G1)–(G2), not the final recognition.
The remaining fusion and amalgam identification belongs to
`qt-i45-g2-recognition`; the Chapter 14 final owner is `qt-d-14414-g2-source`.
Source: Aschbacher–Smith, §I.4, printed p.417, before Lemma I.4.5;
P. Fong and W. J. Wong, *A characterization of the finite simple groups
PSp(4,q), G₂(q), ³D₄(q), I*, Nagoya Math. J. 36 (1969), §2F, pp.153–154,
DOI 10.1017/S0027763000013180.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)
attribute [local instance] G2ThreeConfiguration.H₁_normal G2ThreeConfiguration.H₂_normal
  G2ThreeConfiguration.V_normal V_elementary

omit [Finite G] in
theorem M_quotient_simple : IsSimpleGroup (c.M ⧸ c.V) := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  exact c.quotient_model.some.isSimpleGroup
attribute [local instance] M_quotient_simple

theorem M_normal_subgroups (N : Subgroup c.M) [N.Normal] :
    N = ⊥ ∨ N = c.V ∨ N = ⊤ :=
  GeneralizedFittingEight.normal_subgroup_trichotomy c.V c.fitting
    (V_card c) (quotient_card c) N

theorem M_perfect : Group.IsPerfect c.M :=
  GeneralizedFittingEight.perfect c.V c.fitting (V_card c) (quotient_card c)

theorem M_center : center c.M = ⊥ :=
  GeneralizedFittingEight.center_eq_bot c.V c.fitting (V_card c) (quotient_card c)

theorem M_hom_eq_one {K : Type*} [Group K] (f : c.M →* K)
    (hK : ¬ 7 ∣ Nat.card K) : f = 1 :=
  GeneralizedFittingEight.hom_eq_one_of_seven_not_dvd c.V c.fitting
    (V_card c) (quotient_card c) f hK

theorem ambient_normal_intersection (N : Subgroup G) [N.Normal] :
    N ⊓ c.M = ⊥ ∨ N ⊓ c.M = c.V.map c.M.subtype ∨ N ⊓ c.M = c.M := by
  have h := M_normal_subgroups c (N.subgroupOf c.M)
  rcases h with h | h | h
  · left
    have hh := congrArg (Subgroup.map c.M.subtype) h
    simpa only [subgroupOf_map_subtype, Subgroup.map_bot] using hh
  · right; left
    have hh := congrArg (Subgroup.map c.M.subtype) h
    simpa only [subgroupOf_map_subtype] using hh
  · right; right
    have hh := congrArg (Subgroup.map c.M.subtype) h
    simpa only [subgroupOf_map_subtype, ← MonoidHom.range_eq_map, range_subtype] using hh

private theorem card_inf_le_center {K : Type*} [Group K] [Finite K]
    (A B : Subgroup K) (h : A ≤ centralizer (B : Set K)) :
    Nat.card (A ⊓ B : Subgroup K) ≤ Nat.card (center B) := by
  have hi : A ⊓ B ≤ (center B).map B.subtype := by
    intro x hx
    exact ⟨⟨x, hx.2⟩, mem_center_iff.mpr
      (fun b => Subtype.ext (h hx.1 b b.property)), rfl⟩
  exact (card_le_of_le hi).trans_eq (card_map_of_injective B.subtype_injective)

theorem H_center_card_le_four : Nat.card (center c.H) ≤ 4 := by
  have h₁ : Nat.card c.H₁ = 24 :=
    (Nat.card_congr c.H₁_model.some.toEquiv).trans
      GLS3.Chapter5.SchurPresentation.sl23_card_eq
  have h₂ : Nat.card c.H₂ = 24 :=
    (Nat.card_congr c.H₂_model.some.toEquiv).trans
      GLS3.Chapter5.SchurPresentation.sl23_card_eq
  have hz₁ : Nat.card (center c.H₁) = 2 :=
    (Nat.card_congr (centerCongr c.H₁_model.some).toEquiv).trans
      GLS3.Chapter5.SchurPresentation.sl23_center_card
  have hz₂ : Nat.card (center c.H₂) = 2 :=
    (Nat.card_congr (centerCongr c.H₂_model.some).toEquiv).trans
      GLS3.Chapter5.SchurPresentation.sl23_center_card
  let Z := center c.H
  let J := Z ⊔ c.H₁
  have hZ : Nat.card (Z ⊓ c.H₁ : Subgroup c.H) ≤ 2 := by
    simpa only [hz₁] using card_inf_le_center Z c.H₁ (center_le_centralizer _)
  have hJ : Nat.card (J ⊓ c.H₂ : Subgroup c.H) ≤ 2 := by
    apply (card_inf_le_center J c.H₂ ?_).trans_eq hz₂
    exact sup_le (center_le_centralizer _)
      (fun x hx y hy => (c.commute x hx y hy).symm)
  have hupper : Nat.card (J ⊔ c.H₂ : Subgroup c.H) ≤ 576 :=
    (J ⊔ c.H₂).card_le_card_group.trans_eq (H_card c)
  have hjprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes J c.H₂
    (show c.H₂ ≤ normalizer (J : Set c.H) from le_normalizer_of_normal)
  have hzprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes Z c.H₁
    (show c.H₁ ≤ normalizer (Z : Set c.H) from le_normalizer_of_normal)
  rw [h₂] at hjprod
  rw [h₁] at hzprod
  have hjbound : Nat.card J ≤ 48 := by nlinarith
  change Nat.card Z ≤ 4
  change Nat.card Z * 24 = Nat.card (Z ⊓ c.H₁ : Subgroup c.H) * Nat.card J at hzprod
  nlinarith

theorem not_M_le_normalizer_H : ¬ c.M ≤ normalizer (c.H : Set G) := by
  intro hM
  let f : c.M →* MulAut c.H := c.H.normalizerMonoidHom.comp (inclusion hM)
  let a : c.M →* Equiv.Perm (center c.H) :=
    (MulAut.toPerm (center c.H)).comp ((MulAut.characteristic (center c.H)).comp f)
  have hseven : ¬ 7 ∣ Nat.card (Equiv.Perm (center c.H)) := by
    rw [Nat.card_perm]
    intro hd
    have hdiv : (Nat.card (center c.H)).factorial ∣ Nat.factorial 4 :=
      Nat.factorial_dvd_factorial (H_center_card_le_four c)
    have hbad := hd.trans hdiv
    norm_num at hbad
  have ha := M_hom_eq_one c a hseven
  obtain ⟨z, hz, hH⟩ := exists_involution_centralizer c
  have hzH : z ∈ c.H := by rw [hH]; exact mem_centralizer_singleton_iff.mpr rfl
  have hzZ : (⟨z, hzH⟩ : c.H) ∈ center c.H := by
    apply mem_center_iff.mpr
    intro h
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hH ▸ h.property))
  apply not_M_le_H c
  intro m hm
  rw [hH]
  apply mem_centralizer_singleton_iff.mpr
  have hh := congrArg (fun b : c.M →* Equiv.Perm (center c.H) =>
    (((b ⟨m, hm⟩) ⟨⟨z, hzH⟩, hzZ⟩ : c.H) : G)) ha
  change m * z * m⁻¹ = z at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

theorem H_not_normal : ¬ c.H.Normal := by
  intro h
  let := h
  exact not_M_le_normalizer_H c le_normalizer_of_normal

theorem M_le_normal_of_H_sup_eq_top (N : Subgroup G) [N.Normal]
    (hgen : c.H ⊔ N = ⊤) : c.M ≤ N := by
  have hi : N.index ∣ Nat.card c.H := by
    have he : N.relIndex c.H = N.index := by
      rw [← relIndex_sup_right c.H N, hgen, relIndex_top_right]
    rw [← he]
    exact N.relIndex_dvd_card c.H
  by_contra hMN
  have hn : N.subgroupOf c.M ≠ ⊤ := by
    intro ht
    apply hMN
    intro m hm
    exact (show (⟨m, hm⟩ : c.M) ∈ N.subgroupOf c.M by rw [ht]; trivial)
  have hd := GeneralizedFittingEight.seven_dvd_index_of_proper_normal
    c.V c.fitting (V_card c) (quotient_card c) (N.subgroupOf c.M) hn
  have hseven : 7 ∣ Nat.card c.H :=
    (hd.trans (N.relIndex_dvd_index_of_normal c.M)).trans hi
  rw [H_card c] at hseven
  norm_num at hseven

theorem H_sup_odd_normal_ne_top (N : Subgroup G) [N.Normal]
    (hodd : Odd (Nat.card N)) : c.H ⊔ N ≠ ⊤ := by
  intro hgen
  have hd := card_dvd_of_le (M_le_normal_of_H_sup_eq_top c N hgen)
  rw [M_card c] at hd
  exact hodd.not_two_dvd_nat ((by decide : 2 ∣ 1344).trans hd)

theorem H_sup_oddCore_ne_top : c.H ⊔ pPrimeCore 2 G ≠ ⊤ := by
  apply H_sup_odd_normal_ne_top c
  exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := G))

theorem exists_involution_no_odd_supplement :
    ∃ z : G, orderOf z = 2 ∧ c.H = centralizer ({z} : Set G) ∧
      centralizer ({z} : Set G) ⊔ pPrimeCore 2 G ≠ ⊤ := by
  obtain ⟨z, hz, hH⟩ := exists_involution_centralizer c
  exact ⟨z, hz, hH, hH ▸ H_sup_oddCore_ne_top c⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition

