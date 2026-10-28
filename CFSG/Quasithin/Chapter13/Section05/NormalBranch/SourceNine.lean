module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceStarFull
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceMaximalCore.Alternatives
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The ordinary six-letter conclusion of 13.5.15

The actual starred quotient has order 36, so its Sylow two-subgroups
have order four. The original A₆/S₆ alternatives give |T|=128 or 256,
hence |Q_H|=32 or 64. In the first case Q_H=U_H. In the second case
the proved product Q_H=U_H C_T(L₁), with intersection V₁ of order two,
gives |C_T(L₁)|=4. Every subgroup and quotient is the original source one.

Source: Aschbacher–Smith 13.5.15(9), printed pp.920–921.
The preceding equality O₂(LT)=V and maximal two-locality remain explicit
here; SourceSevenNine supplies them from the original earlier input.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceNine
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}

theorem sylow_card_eq_four_mul_core (h : D.Hypothesis)
    (hs : Nat.card (Section08.Source.Hstar D.H) = 36) :
    Nat.card D.T = Nat.card D.QH * 4 := by
  let P := D.T.subtype h.T_le_H
  let π := QuotientGroup.mk' (pCore 2 D.H)
  let S : Sylow 2 (Section08.Source.Hstar D.H) := P.mapSurjective (QuotientGroup.mk'_surjective _)
  have hS : Nat.card S = 4 := by
    rw [S.card_eq_multiplicity, hs]
    decide +kernel
  have hc := relIndex_mul_relIndex (⊥ : Subgroup D.H) (pCore 2 D.H)
    (P : Subgroup D.H) bot_le (pCore_isPGroup.le_sylow_of_normal P)
  simp only [relIndex_bot_left] at hc
  have him : (pCore 2 D.H).relIndex (P : Subgroup D.H) = 4 := by
    rw [←QuotientGroup.ker_mk' (pCore 2 D.H), relIndex_ker]
    exact hS
  rw [him] at hc
  have hP : Nat.card P = Nat.card D.T :=
    Nat.card_congr (subgroupOfEquivOfLe h.T_le_H).toEquiv
  have hQ : Nat.card D.QH = Nat.card (pCore 2 D.H) :=
    card_map_of_injective D.H.subtype_injective
  rw [hP,←hQ] at hc
  exact hc.symm

open Section08.SourceCompletion
variable {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
include d h e hseed hn hU

/-- The complete ordinary six-letter conclusion, with the original starred quotient. -/
theorem source13_5_15_nine (hQ : D.LT.pCoreIn 2 = D.V)
    (hmax : IsMaximalTwoLocal M) :
    Nonempty (Section08.Source.Hstar D.H ≃* OmegaPlusFour) ∧
    ((M = D.L ∧ D.QH = D.UH) ∨
      (Nonempty ((M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 6)) ∧
        D.QH = D.UH ⊔ ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G)) ∧
        Nat.card ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G) : Subgroup G) = 4)) := by
  refine ⟨SourceStarFull.original_star_model d h e hseed hn hU hQ,?_⟩
  have hcard := sylow_card_eq_four_mul_core h
    (SourceStarFull.original_star_card d h e hseed hn hU hQ)
  have hUcard := (SourceQuaternion.source13_5_15_five d h e hseed hn hU).2.1
  rcases SourceMaximalCore.maximal_model_and_sylow_order d h e hseed hn hU hQ hmax with
    ⟨he,hT⟩ | ⟨he,hT⟩
  · left
    exact ⟨he,(eq_of_le_of_card_ge h.UH_le_QH (by omega)).symm⟩
  · right
    refine ⟨he,SourceQuaternionCentralizer.core_eq_closure_sup_local_centralizer
      d h e hseed hn hU,?_⟩
    let C := (D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G)
    have hUL := (closure_reduction h hseed hn).2.2
    have hUC : C ≤ centralizer (D.UH : Set G) := inf_le_right.trans
      (centralizer_le ((closure_reduction h hseed hn).2.1.trans (pCoreIn_le 2 D.L₁)))
    have hmeet : D.UH ⊓ C = D.V₁ := by
      have hc := SourceCoreIntersection.local_centralizer_inf_local d h e hseed hn hU hQ
      apply le_antisymm
      · rintro x ⟨hx,hc'⟩
        exact hc.le ⟨hc',hUL hx⟩
      · exact le_inf (h.point_lt.le.trans (le_conjugateSpanBy _ _))
          (hc.ge.trans inf_le_left)
    have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes D.UH C
      (hUC.trans (Subgroup.centralizer_le_normalizer _))
    rw [hmeet,h.point_card,←SourceQuaternionCentralizer.core_eq_closure_sup_local_centralizer
      d h e hseed hn hU,hUcard] at hprod
    change Nat.card C = 4
    omega

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceNine
