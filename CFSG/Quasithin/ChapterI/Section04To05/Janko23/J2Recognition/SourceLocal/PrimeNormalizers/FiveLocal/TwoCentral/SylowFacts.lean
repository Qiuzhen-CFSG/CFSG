module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.Preparation
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Sylow five-subgroups from a root-family normalizer

A Sylow five-subgroup containing a root-family member lies in its literal
normalizer, modeled by D₁₀ × A₅. Its order is 25, so the order of each of
its coordinate images divides five. Both projections are nontrivial:
otherwise an order-25 group would embed in a group of order ten or sixty.

The centralizer of a nonidentity five-element in each factor has exponent
five. The A₅ assertion follows from the centralizer of a full five-cycle.
Consequently the ambient centralizer of the Sylow subgroup is itself a
five-group; Sylow maximality gives equality. Sylow conjugacy transfers this
to every Sylow subgroup, also proving elementary abelianness.

This proves the Sylow assertions used in the middle paragraph of Aschbacher,
*Sporadic Groups* (1994), 47.2, printed p.261. The two-central normalizer
and the separation of the two five-families are not assumed or proved here.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem a5_five_centralizer (a b : alternatingGroup (Fin 5))
    (ha : a ^ 5 = 1) (hne : a ≠ 1) (hcomm : Commute a b) : b ^ 5 = 1 := by
  have hao : orderOf a = 5 := orderOf_eq_prime ha hne
  have hσ : orderOf (a : Equiv.Perm (Fin 5)) = 5 := (orderOf_coe a).trans hao
  have hc : (a : Equiv.Perm (Fin 5)).IsCycle :=
    Equiv.Perm.isCycle_of_prime_order (by rw [hσ]; decide)
      (by have h := Finset.card_le_univ (a : Equiv.Perm (Fin 5)).support
          simp only [Fintype.card_fin] at h
          rw [hσ]
          omega)
  have hs : (a : Equiv.Perm (Fin 5)).support = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa only [Fintype.card_fin, ← hc.orderOf] using hσ
  obtain ⟨hinv, k, hk⟩ := hc.commute_iff.mp (hcomm.symm.map (alternatingGroup (Fin 5)).subtype)
  have hb : (a : Equiv.Perm (Fin 5)) ^ k = b := by
    apply Equiv.Perm.ext
    intro x
    exact (Equiv.Perm.congr_fun hk x).trans
      (Equiv.Perm.ofSubtype_subtypePerm_of_mem hinv (by rw [hs]; exact Finset.mem_univ x))
  apply Subtype.ext
  change (b : Equiv.Perm (Fin 5)) ^ 5 = 1
  rw [← hb, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  have hap : (a : Equiv.Perm (Fin 5)) ^ (5 : ℤ) = 1 := by
    exact_mod_cast congrArg Subtype.val ha
  change ((a : Equiv.Perm (Fin 5)) ^ (5 : ℤ)) ^ k = 1
  rw [hap, one_zpow]

private theorem d10_five_centralizer (a b : DihedralGroup 5)
    (ha : a ^ 5 = 1) (hne : a ≠ 1) (hcomm : Commute a b) : b ^ 5 = 1 := by
  revert a b
  change ∀ a b : DihedralGroup 5, a ^ 5 = 1 → a ≠ 1 → a * b = b * a → b ^ 5 = 1
  decide +kernel

private theorem model_pow_five {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H = 25) (f : H →* DihedralGroup 5 × alternatingGroup (Fin 5))
    (x : H) : (f x) ^ 5 = 1 := by
  have h₁ : orderOf (f x).1 ∣ 25 := by
    exact hH ▸ (orderOf_map_dvd ((MonoidHom.fst _ _).comp f) x).trans
      (orderOf_dvd_natCard x)
  have h₂ : orderOf (f x).2 ∣ 25 := by
    exact hH ▸ (orderOf_map_dvd ((MonoidHom.snd _ _).comp f) x).trans
      (orderOf_dvd_natCard x)
  have hc₁ : orderOf (f x).1 ∣ 10 := by
    simpa only [DihedralGroup.nat_card] using orderOf_dvd_natCard (f x).1
  have hc₂ : orderOf (f x).2 ∣ 60 := by
    simpa only [CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.card_A5]
      using orderOf_dvd_natCard (f x).2
  exact Prod.ext
    (orderOf_dvd_iff_pow_eq_one.mp (show orderOf (f x).1 ∣ 5 from Nat.dvd_gcd h₁ hc₁))
    (orderOf_dvd_iff_pow_eq_one.mp (show orderOf (f x).2 ∣ 5 from Nat.dvd_gcd h₂ hc₂))

private theorem model_centralizer_pow_five {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H = 25) (f : H →* DihedralGroup 5 × alternatingGroup (Fin 5))
    (hf : Function.Injective f) (b : DihedralGroup 5 × alternatingGroup (Fin 5))
    (hcomm : ∀ x, Commute (f x) b) : b ^ 5 = 1 := by
  have h₁ : ∃ x, (f x).1 ≠ 1 := by
    by_contra! h
    have hi : Function.Injective ((MonoidHom.snd _ _).comp f) := by
      intro x y hxy
      exact hf (Prod.ext ((h x).trans (h y).symm) hxy)
    have hd := card_dvd_of_injective ((MonoidHom.snd _ _).comp f) hi
    rw [hH, CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.card_A5] at hd
    norm_num at hd
  have h₂ : ∃ x, (f x).2 ≠ 1 := by
    by_contra! h
    have hi : Function.Injective ((MonoidHom.fst _ _).comp f) := by
      intro x y hxy
      exact hf (Prod.ext hxy ((h x).trans (h y).symm))
    have hd := card_dvd_of_injective ((MonoidHom.fst _ _).comp f) hi
    rw [hH, DihedralGroup.nat_card] at hd
    norm_num at hd
  obtain ⟨x, hx⟩ := h₁
  obtain ⟨y, hy⟩ := h₂
  exact Prod.ext
    (d10_five_centralizer (f x).1 b.1 (congrArg Prod.fst (model_pow_five hH f x)) hx
      ((hcomm x).map (MonoidHom.fst _ _)))
    (a5_five_centralizer (f y).2 b.2 (congrArg Prod.snd (model_pow_five hH f y)) hy
      ((hcomm y).map (MonoidHom.snd _ _)))

/-- The actual product normalizer forces exponent five and self-centralization. -/
theorem sylow_facts_of_root_member {G : Type*} [Group G] [Finite G]
    {D : Seed G} (hG : Nat.card G = 604800) {E : Subgroup G}
    (W : RootFiveWitness D E) (P : Sylow 5 G) (hEP : E ≤ (P : Subgroup G)) :
    IsElementaryAbelian 5 P ∧ centralizer (P : Set G) = (P : Subgroup G) := by
  have hPN : (P : Subgroup G) ≤ normalizer (E : Set G) :=
    (sylow_le_centralizer hG P E hEP).trans (centralizer_le_normalizer _)
  let f : P →* DihedralGroup 5 × alternatingGroup (Fin 5) :=
    W.equiv.toMonoidHom.comp (inclusion hPN)
  have hf : Function.Injective f := W.equiv.injective.comp (inclusion_injective hPN)
  have hpow (x : P) : x ^ 5 = 1 := by
    apply hf
    rw [map_pow, map_one]
    exact model_pow_five (sylow_card hG P) f x
  refine ⟨{ toIsMulCommutative := sylow_commutative hG P,
             exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }, ?_⟩
  have hCN : centralizer (P : Set G) ≤ normalizer (E : Set G) :=
    (centralizer_le hEP).trans (centralizer_le_normalizer _)
  apply P.is_maximal' _ (sylow_le_centralizer hG P P le_rfl)
  intro x
  refine ⟨1, ?_⟩
  have hx := model_centralizer_pow_five (sylow_card hG P) f hf
    (W.equiv (inclusion hCN x)) (fun y => ?_)
  · apply Subtype.ext
    have h : (inclusion hCN x) ^ 5 = 1 := by
      apply W.equiv.injective
      simpa only [map_pow, map_one] using hx
    change (x : G) ^ 5 = 1
    exact congrArg Subtype.val h
  · apply (show Commute (inclusion hPN y) (inclusion hCN x) from ?_).map W.equiv
    exact Subtype.ext (x.property y y.property)

/-- Every ambient Sylow five-subgroup contains a member of the root-four family. -/
theorem exists_root_member_in_sylow {G : Type*} [Group G] [Finite G]
    {D : Seed G} (S : SourceLocal.InvolutionGeometry.SelectedGeometry D)
    (P : Sylow 5 G) : ∃ E : Subgroup G, FiveCentralizing S.t E ∧ E ≤ (P : Subgroup G) := by
  have ht : 5 ^ (Nat.card (CFSG.Quasithin.Janko23.involutionCentralizer S.t)).factorization 5 = 5 := by
    rw [S.model.centralizer_card]
    decide +kernel
  obtain ⟨E, hE, hEt⟩ := exists_fiveCentralizing S.t ht
  obtain ⟨Q, hEQ⟩ := (IsPGroup.of_card (p := 5) (n := 1) hE).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨E.map (MulAut.conj g).toMonoidHom, ?_, ?_⟩
  · apply (fiveCentralizing_iff_mem_orbit S.t ht E hE hEt _).mpr
    exact ⟨ConjAct.toConjAct g, rfl⟩
  · have hmap : (Q : Subgroup G).map (MulAut.conj g).toMonoidHom = (P : Subgroup G) :=
      congrArg (fun R : Sylow 5 G => (R : Subgroup G)) hg
    rw [← hmap]
    exact map_mono hEQ

/-- Both Sylow conclusions of the two-central branch, using only the root-family input. -/
theorem sylow_facts_of_root_family {G : Type*} [Group G] [Finite G]
    {D : Seed G} (hG : Nat.card G = 604800)
    (S : SourceLocal.InvolutionGeometry.SelectedGeometry D) (hA : RootFiveFamily D S.t)
    (P : Sylow 5 G) :
    IsElementaryAbelian 5 P ∧ centralizer (P : Set G) = (P : Subgroup G) := by
  obtain ⟨E, hE, hEP⟩ := exists_root_member_in_sylow S P
  obtain ⟨W⟩ := hA E hE
  exact sylow_facts_of_root_member hG W P hEP

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral
