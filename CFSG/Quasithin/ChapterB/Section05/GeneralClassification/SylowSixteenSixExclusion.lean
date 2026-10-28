module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SylowSixteenSectionLift
public import Theory.Representation.BinaryAlternatingSixSmallDegrees
import all CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SylowSixteenFactors

/-!
# Excluding the ordinary A6 fitting component on the original six-space

The genuine B.5 moved section equals the whole original module. Its
irreducible case cannot have group A6 and degree6, by the proved binary
small-degree theorem. The doubled linear-three and higher binary-linear
cases are excluded by their actual group or module markings. The cubic
center is not discarded: this argument concerns ordinary A6 only.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction.SylowSixteenSixSpace
open QuasisimpleSource
variable {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem not_ordinary_six_source (ρ : Representation (ZMod 2) D V)
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (hd : Module.finrank (ZMod 2) V=6)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ)))
    (e : generalizedFitting (offenderSubgroup ρ)≃*alternatingGroup (Fin 6)) : False := by
  let J := offenderSubgroup ρ
  let F := generalizedFitting J
  let s := c.sectionData
  obtain ⟨hs,_⟩ := fitting_section_full ρ hf hi hq s
  obtain ⟨b,_⟩ := fitting_section_equiv ρ hf hi hq s
  have hspace : Module.finrank (ZMod 2) s.space.toSubmodule=6 := by
    rw [hs,finrank_top,hd]
  have hquot : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule)=6 :=
    b.finrank_eq.symm.trans hd
  have hF : Nat.card F=360 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  cases c.clause_one with
  | irreducible _ _ hirr _ _ =>
    let σ := s.central.quotientRepresentation.comp F.subtype
    let : Representation.IsIrreducible σ := hirr
    let τ := σ.comp e.symm.toMonoidHom
    let : Representation.IsIrreducible τ :=
      (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective σ).mpr hirr
    have hh := AlternatingSix.BinarySmallDegrees.finrank_eq_one_or_four τ hquot.le
    omega
  | doubleThree K _ a _ _ =>
    have small (S : Sylow 2 F) : Nat.card S≤16 := by
      rw [S.card_eq_multiplicity,hF]
      decide +kernel
    have hc := linearThree_factor_card small (⊤ : Subgroup F) K
      ((Subgroup.topEquiv : (⊤ : Subgroup F)≃*F).trans a.groupEquiv)
    rw [card_top,hF] at hc
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

end CFSG.Quasithin.ChapterB.SourceInduction.SylowSixteenSixSpace
