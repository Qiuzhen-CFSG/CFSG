module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SylowSixteenCubicReduction
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.HexacodeEven
public import Theory.Alternating.OddCentralCovers
import all CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SylowSixteenFactors

/-!
# The actual cubic fitting action has hexacode coordinates

The B.5 section is the whole original six-space with no central attachment.
The other clause-one module structures have incompatible dimensions or
orders, so the actual cubic fitting restriction is irreducible. The proved
triple-cover comparison and even hexacode recognition give a single group
and vector marking on this literal component.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Atlas.Codes
namespace CFSG.Quasithin.ChapterB.SourceInduction.SylowSixteenSixSpace
open QuasisimpleSource
variable {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem cubic_fitting_actionEquiv (ρ : Representation (ZMod 2) D V)
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (hd : Module.finrank (ZMod 2) V=6)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ)))
    (hc : Nat.card (center (generalizedFitting (offenderSubgroup ρ)))=3)
    (eq : (generalizedFitting (offenderSubgroup ρ) ⧸
      center (generalizedFitting (offenderSubgroup ρ)))≃*alternatingGroup (Fin 6)) :
    Nonempty (ActionEquiv
      ((ρ.comp (offenderSubgroup ρ).subtype).comp (generalizedFitting (offenderSubgroup ρ)).subtype)
      Hexacode.evenAction) := by
  let J := offenderSubgroup ρ
  let F := generalizedFitting J
  let s := c.sectionData
  let := hq
  obtain ⟨q⟩ := GLS3.Chapter5.OddCentralCovers.triple_six_equiv_hexacode eq hc
  have hF : Nat.card F=1080 := (Nat.card_congr q.toEquiv).trans hexEven_card
  obtain ⟨hs,_⟩ := fitting_section_full ρ hf hi hq s
  obtain ⟨b,hb⟩ := fitting_section_equiv ρ hf hi hq s
  have hspace : Module.finrank (ZMod 2) s.space.toSubmodule=6 := by
    rw [hs,finrank_top,hd]
  have hquot : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule)=6 :=
    b.finrank_eq.symm.trans hd
  have hirr : Representation.IsIrreducible (s.central.quotientRepresentation.comp F.subtype) := by
    cases c.clause_one with
    | irreducible _ _ hh _ _ => exact hh
    | doubleThree K _ a _ _ =>
      have small (S : Sylow 2 F) : Nat.card S≤16 := by
        rw [S.card_eq_multiplicity,hF]
        decide +kernel
      have hh := linearThree_factor_card small (⊤ : Subgroup F) K
        ((Subgroup.topEquiv : (⊤ : Subgroup F)≃*F).trans a.groupEquiv)
      rw [card_top,hF] at hh
      omega
    | naturalDual d hdd _ hn =>
      obtain ⟨a⟩ := hn
      have hh : Module.finrank (ZMod 2) s.space.toSubmodule=d+d := by
        rw [a.linearEquiv.finrank_eq]
        change Module.finrank (ZMod 2)
          ((Fin d→ZMod 2) × Module.Dual (ZMod 2) (Fin d→ZMod 2))=d+d
        rw [Module.finrank_prod,Subspace.dual_finrank_eq]
        simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin]
      rcases hdd with rfl | rfl <;> omega
    | repeatedNatural d r hdd _ _ _ hn =>
      obtain ⟨a⟩ := hn
      have hh : Module.finrank (ZMod 2) s.space.toSubmodule=r*d := by
        rw [a.linearEquiv.finrank_eq]
        change Module.finrank (ZMod 2) (Fin r→Fin d→ZMod 2)=r*d
        simp only [Module.finrank_pi_fintype,Module.finrank_self,Fintype.card_fin,
          Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one]
      rcases hdd with rfl | rfl <;> omega
  let σ := (s.central.quotientRepresentation.comp F.subtype).comp q.symm.toMonoidHom
  have hfaith : Function.Injective (s.central.quotientRepresentation.comp F.subtype) := by
    intro f g hfg
    apply F.subtype_injective
    apply J.subtype_injective
    apply hf
    ext v
    apply b.injective
    change b (ρ f.val.val v)=b (ρ g.val.val v)
    rw [hb,hb]
    exact LinearMap.congr_fun hfg (b v)
  have hσ : Representation.IsIrreducible σ :=
    (irreducible_comp_surjective_iff q.symm.toMonoidHom q.symm.surjective _).mpr hirr
  obtain ⟨a⟩ := ChapterK.Alternating.EvenRecognition.exists_actionEquiv σ
    (hfaith.comp q.symm.injective) hσ hquot
  refine ⟨q.trans a.groupEquiv,b.trans a.linearEquiv,?_⟩
  intro f v
  change a.linearEquiv (b (ρ f.val.val v))=
    Hexacode.evenAction (a.groupEquiv (q f)) (a.linearEquiv (b v))
  rw [hb]
  have hh := a.intertwines (q f) (b v)
  simpa only [σ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,q.symm_apply_apply,Subgroup.subtype_apply] using hh

end CFSG.Quasithin.ChapterB.SourceInduction.SylowSixteenSixSpace
