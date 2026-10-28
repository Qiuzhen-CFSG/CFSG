module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import GorensteinWalter.PSL2Cardinality
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.Mathieu.M24.TwoLocalExtensions

/-!
# M₂₄ is absent from the full FF group catalogue

The two-part of the checked M₂₄ order bounds the binary field degrees through
the concrete unipotent subgroups. The remaining orders differ, while SL₅(2)
has a factor 31. The triple-six case retains its actual cubic center.

This supplies the local M₂₄ exclusion in the J₄ branch of Aschbacher--Smith
15.1.20(3), printed p.1097, using the full C.2.7 group catalogue. It does
not require the separate placement of a local-family Borel subgroup.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.C27Source.StarModels
open ChapterB.QuasisimpleSource

private theorem m24_two_power {k : ℕ} (hd : 2 ^ k ∣ Nat.card Sporadic.Mathieu.M24) : k ≤ 10 := by
  by_contra hn
  have hh := (pow_dvd_pow 2 (by omega : 11 ≤ k)).trans hd
  rw [Sporadic.Mathieu.m24_order] at hh
  norm_num at hh

/-- No group in the full FF catalogue is isomorphic to the concrete M₂₄ carrier. -/
theorem not_mathieuTwentyFour {A : Type*} [Group A]
    (h : StarModels.Model A) (e : A ≃* Sporadic.Mathieu.M24) : False := by
  have hc : Nat.card A = 244823040 := (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m24_order
  cases h with
  | linearTwo F f =>
    have hd : 2 ^ F.degree ∣ Nat.card Sporadic.Mathieu.M24 := by
      rw [←Nat.card_congr e.toEquiv,Nat.card_congr f.toEquiv,
        GorensteinWalter.sl2_card_formula,F.card_eq]
      exact dvd_mul_right _ _
    have hb := m24_two_power hd
    rw [Nat.card_congr f.toEquiv,GorensteinWalter.sl2_card_formula,F.card_eq] at hc
    have hn := F.degree_pos
    generalize F.degree = n at *
    interval_cases n <;> norm_num at hc
  | linearThree F f =>
    have hd := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
    rw [Matrix.PSL3.LinearThree.card_unipotentSL,F.card_eq,←pow_mul] at hd
    have hb := m24_two_power (hd.trans (by
      rw [←Nat.card_congr e.toEquiv,Nat.card_congr f.toEquiv]))
    rw [Nat.card_congr f.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,F.card_eq] at hc
    have hn := F.degree_pos
    generalize F.degree = n at *
    have : n ≤ 3 := by omega
    interval_cases n <;> norm_num at hc
  | symplectic F hl f =>
    have hd := (Theory.SpecificGroups.SymplecticFour.unipotent (F := F.Carrier)).card_subgroup_dvd_card
    rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,F.card_eq,←pow_mul] at hd
    have hb := m24_two_power (hd.trans (by
      rw [←Nat.card_congr e.toEquiv,Nat.card_congr f.toEquiv]))
    have hn : F.degree = 2 := by omega
    rw [Nat.card_congr f.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,F.card_eq,hn] at hc
    norm_num at hc
  | g2 F hl f =>
    have hd := (Atlas.G2.unipotent (K := F.Carrier)).card_subgroup_dvd_card
    rw [Atlas.G2.card_unipotent,F.card_eq,←pow_mul] at hd
    have hb := m24_two_power (hd.trans (by
      rw [←Nat.card_congr e.toEquiv,Nat.card_congr f.toEquiv]))
    omega
  | g2DerivedTwo f =>
    rw [Nat.card_congr f.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hc
    norm_num at hc
  | alternating n hn f =>
    rw [Nat.card_congr f.toEquiv] at hc
    have : Nontrivial (Fin n) := by
      rcases hn with rfl | rfl | rfl | rfl <;> infer_instance
    have hh := two_mul_nat_card_alternatingGroup (α := Fin n)
    rw [Nat.card_perm,Nat.card_fin,hc] at hh
    rcases hn with rfl | rfl | rfl | rfl <;> norm_num at hh
  | linearFiveTwo f =>
    have hpsl := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
    norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Fin.val_zero, Fin.val_succ, Nat.mul_one] at hpsl
    have hd : 31 ∣ Nat.card A := by
      rw [Nat.card_congr f.toEquiv]
      apply dvd_trans _ (card_quotient_dvd_card (center SL(5,ZMod 2)))
      rw [hpsl]
      norm_num [Fin.prod_univ_succ]
    rw [hc] at hd
    norm_num at hd
  | tripleSix f g =>
    have hz : Nat.card (center A) = 3 := (Nat.card_congr f.toEquiv).trans (by simp)
    have hh := card_eq_card_quotient_mul_card_subgroup (center A)
    rw [hz,hc,Nat.card_congr g.toEquiv] at hh
    have ha := two_mul_nat_card_alternatingGroup (α := Fin 6)
    norm_num only [Nat.card_perm,Nat.card_fin, Nat.factorial] at ha
    omega

end CFSG.Quasithin.ChapterC.C27Source.StarModels
