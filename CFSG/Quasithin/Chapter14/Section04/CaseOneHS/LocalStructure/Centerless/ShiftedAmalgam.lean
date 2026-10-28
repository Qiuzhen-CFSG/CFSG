module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.ResidualPair

/-!
# The shifted involution and its centralizer quotient

From the original flag, choose one pair of conjugators that supplies both
plane geometry and residual generation. Assuming the earlier seed exclusion
Z(LT) ∩ U = 1, the shifted center is disjoint from Z(U) and centralizes it.
A central Sylow involution e in Z(I₂) therefore gives the actual shifted
actor a = eˡ and K = ⟨aᴴ⟩ centralizing Z(U). This places Ke = ⟨KT,I₂T⟩
inside C_G(e), so its point orbit Ue is reduced and Ke/C_Ke(Ue) has trivial
two-core.

This is the literal application of the shifted-center results to the
opening of 14.3.31. It does not supply the Goldschmidt-amalgam hypotheses
or the concluding dimension contradiction. The explicit 14.3.25 seed
exclusion and the remaining 14.3.29--31 arguments stay with
qt-d-hs-centerless-source; final LocalStructure assembly stays with
qt-d-hs-local-structure. No conclusion of 14.3.32 is used here.

Source: Aschbacher--Smith, 14.3.28 and 14.3.31, printed pp.1002--1003.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The source shifted actor and its literal centralizer quotient, with all
geometric and centralization premises discharged from 14.3.25. -/
theorem source_shifted_amalgam_of_seed (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ g l e : G, g ∈ L ∧ g ∈ F.P L ∧ g ∉ F.H ∧ l ∈ L ∧
      l ∈ centralizer (conjugate (F.Vi 1) g : Set G) ∧
      V = F.Vi 2 ⊔ conjugate (F.Vi 1) l ∧
      L = F.orderedResidual L 1 ⊔ conjugate (F.orderedResidual L 1) l ∧
      Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) =
        conjugate F.ZU g ⊓ conjugate F.ZU l ∧
      F.ZU ⊓ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) = ⊥ ∧
      orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧ e ∈ F.ZU ∧ e ∉ F.Vi 1 ∧
      let a := l⁻¹ * e * l
      let K := conjugateSpanBy (zpowers a) F.H
      orderOf a = 2 ∧ a ∈ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) ∧
        K ≤ centralizer (F.ZU : Set G) ∧
        amalgamGroup F L K ≤ centralizer ({e} : Set G) ∧
        IsPReduced 2 ((amalgamModule F L K).subgroupOf (amalgamGroup F L K)) ∧
        pCore 2 (AmalgamQuotient F L K) = ⊥ := by
  obtain ⟨g, l, hgL, hgP, hgH, hlL, hlC, _, hspace, _, hgen⟩ :=
    source_shifted_generating_geometry d earlier hq chosen structural F
  have hdis := source_shifted_disjoint_of_residual_pair d earlier hq chosen structural
    alternatives F hne hseed g hgP hgH l hlC hgen
  have hc := source_shifted_center_centralizes d earlier hq chosen structural alternatives
    F hne hseed g hgP hgH l hlL hlC hgen
  obtain ⟨e, he, heI, heT, heU, heV⟩ :=
    source_center_involution d earlier hq chosen structural alternatives F hne hI
  have haI : l⁻¹ * e * l ∈ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) := by
    rw [centerIn_conjugate]
    simpa only [conjugate, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      mem_map_of_mem (MulAut.conj l⁻¹).toMonoidHom heI
  have hK := actor_span_centralizes F (l⁻¹ * e * l) (hc haI)
  refine ⟨g, l, e, hgL, hgP, hgH, hlL, hlC, hspace, hgen,
    source_shifted_center_intersection d earlier hq chosen structural alternatives
      F hne g hgP hgH l hlC, hdis, he, heI, heT, heU, heV, ?_, haI, hK,
    amalgamGroup_le_centralizer F _ e heI heT heU hK,
    source_amalgam_reduced d chosen F _ e he heI heT heU hK,
    source_amalgam_quotient_core d chosen F _ e he heI heT heU hK⟩
  have hh := (MulAut.conj l⁻¹).orderOf_eq e
  simpa only [MulAut.conj_apply, inv_inv, he] using hh

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
