module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableQuotient
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree

/-!
# The original solvable amalgam modulo its prime-to-three core

Apply F.6.11 to the literal orbit-action quotient Ke/C_Ke(Ue). The
collapsed branch would make both embedded local two-cores equal, contrary
to the proved Thompson escape. The surviving branch preserves the entire
Sylow overlap. Its quotient map is injective on both local groups because
the original action quotient has trivial two-core; the distinct local
cores therefore remain distinct through this second quotient as well.

The source application retains the original involution, reduced orbit
module and FF action. It prepares the original inputs to F.6.18; it does
not assert the classification exclusions or their dimension contradiction.
Those and the final source_centerless assembly remain with this owner.
Source: Aschbacher--Smith 14.3.31, printed p.1003, and F.6.11, pp.306--307.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u

private theorem prime_quotient_of_distinct_cores
    {D : Type u} [Group D] [Finite D] (A B : Subgroup D)
    (h : ChapterF.IsGoldschmidtTriple A B) (hcore : pCore 2 D = ⊥)
    (hne : B.pCoreIn 2 ≠ A.pCoreIn 2) :
    let p := QuotientGroup.mk' (pPrimeCore 3 D)
    ChapterF.IsGoldschmidtTriple (A.map p) (B.map p) ∧
      (A.map p) ⊓ (B.map p) = (A ⊓ B).map p ∧
      pCore 2 (D ⧸ pPrimeCore 3 D) = ⊥ ∧
      Function.Injective (p.subgroupMap A) ∧ Function.Injective (p.subgroupMap B) ∧
      (B.map p).pCoreIn 2 ≠ (A.map p).pCoreIn 2 := by
  rcases h.primeToThreeCore_dichotomy with ⟨hi,ht,hc,_⟩ | ⟨ha,hb,_⟩
  · let p := QuotientGroup.mk' (pPrimeCore 3 D)
    have hk (C : Subgroup D) (hC : C ≤ A ∨ C ≤ B) : (p.subgroupMap C).ker = ⊥ := by
      rcases hC with hC | hC
      · rw [h.primeToThreeCore_subgroup_kernel C hC,hcore,bot_subgroupOf]
      · rw [h.symm.primeToThreeCore_subgroup_kernel C hC,hcore,bot_subgroupOf]
    have ha : IsPGroup 2 (p.subgroupMap A).ker := hk A (Or.inl le_rfl) ▸ IsPGroup.of_bot
    have hb : IsPGroup 2 (p.subgroupMap B).ker := hk B (Or.inr le_rfl) ▸ IsPGroup.of_bot
    exact ⟨ht,hi,hc,(p.subgroupMap A).ker_eq_bot_iff.mp (hk A (Or.inl le_rfl)),
      (p.subgroupMap B).ker_eq_bot_iff.mp (hk B (Or.inr le_rfl)),
      pCoreIn_image_ne_of_local_kernels 2 p B A hb ha
        (h.symm.local_twoCore_le_intersection.trans inf_le_right)
        (h.local_twoCore_le_intersection.trans inf_le_right) hne⟩
  · exact (hne (hb.trans ha.symm)).elim

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne

/-- F.6.11 preserves the two actual quotient vertices and their entire overlap. -/
theorem source_solvable_primeToThree_amalgam
    (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ l e : G, l ∈ L ∧ orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧
      let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
      let E := amalgamGroup F L K
      let q := QuotientGroup.mk' (amalgamKernel F L K)
      let A := ((K ⊔ (T : Subgroup G)).subgroupOf E).map q
      let B := ((F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E).map q
      let p := QuotientGroup.mk' (pPrimeCore 3 (AmalgamQuotient F L K))
      ∃ hr : IsPReduced 2 ((amalgamModule F L K).subgroupOf E),
      let _ := hr.elementary
      ChapterF.IsGoldschmidtTriple A B ∧ B.pCoreIn 2 ≠ A.pCoreIn 2 ∧
      pCore 2 (AmalgamQuotient F L K) = ⊥ ∧
      E ≤ centralizer ({e} : Set G) ∧
      Representation.BinaryOffender.IsFFModule
        (Representation.NormalElementaryQuotient.representation
          ((amalgamModule F L K).subgroupOf E) q (QuotientGroup.mk'_surjective _)
          (QuotientGroup.ker_mk' _)) ∧
      ChapterF.IsGoldschmidtTriple (A.map p) (B.map p) ∧
      A.map p ⊓ B.map p = (A ⊓ B).map p ∧
      pCore 2 (AmalgamQuotient F L K ⧸ pPrimeCore 3 (AmalgamQuotient F L K)) = ⊥ ∧
      Function.Injective (p.subgroupMap A) ∧ Function.Injective (p.subgroupMap B) ∧
      (B.map p).pCoreIn 2 ≠ (A.map p).pCoreIn 2 := by
  obtain ⟨l,e,hl,he,heI,heT,hr,hgold,hneq,hcore,hE,hff⟩ :=
    source_solvable_goldschmidt_ff d earlier hq chosen structural alternatives F hne hZ model hI
  exact ⟨l,e,hl,he,heI,heT,hr,hgold,hneq,hcore,hE,hff,
    prime_quotient_of_distinct_cores _ _ hgold hcore hneq⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
