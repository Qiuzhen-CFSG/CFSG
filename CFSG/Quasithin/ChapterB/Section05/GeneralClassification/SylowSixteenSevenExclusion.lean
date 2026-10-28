module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SylowSixteenSectionLift
import all CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SylowSixteenFactors
import all CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.SmallModels

/-!
# The actual seven row is excluded by the original fixed line

The full B.5 source retains its action marking. On the original six-space,
its A7 row is the deleted seven-letter action: the other marked group and
module possibilities have incompatible orders or dimensions. Every
2-subgroup of its full normalizer fixes at least a plane, contradicting
the literal extraspecial-kernel image, whose fixed space is the original
one-dimensional center. No full ambient normalizer model is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.SourceInduction.SylowSixteenSixSpace
open QuasisimpleSource
variable {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem not_seven_source (ρ : Representation (ZMod 2) D V)
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (hd : Module.finrank (ZMod 2) V=6)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ)))
    (e : generalizedFitting (offenderSubgroup ρ)≃*alternatingGroup (Fin 7))
    (A : Subgroup D) (hA : IsPGroup 2 A)
    (hfix : Module.finrank (ZMod 2) (fixedSpace ρ A)=1) : False := by
  let J := offenderSubgroup ρ
  let F := generalizedFitting J
  let s := c.sectionData
  obtain ⟨hs,_⟩ := fitting_section_full ρ hf hi hq s
  obtain ⟨b,_⟩ := fitting_section_equiv ρ hf hi hq s
  have hspace : Module.finrank (ZMod 2) s.space.toSubmodule=6 := by
    rw [hs,finrank_top,hd]
  have hquot : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule)=6 :=
    b.finrank_eq.symm.trans hd
  have hF : Nat.card F=2520 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have small (S : Sylow 2 F) : Nat.card S≤16 := by
    rw [S.card_eq_multiplicity,hF]
    decide +kernel
  have noAlt {n : ℕ} [NeZero n] (hn : n=5 ∨ n=6 ∨ n=8)
      (a : F≃*alternatingGroup (Fin n)) : False := by
    rcases hn with rfl | rfl | rfl <;>
      rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup] at hF <;>
      norm_num [Nat.factorial] at hF
  have noLinearThree (K : BinaryField) (a : F≃*SL(3,K.Carrier)) : False := by
    have hh := linearThree_factor_card small (⊤ : Subgroup F) K
      ((Subgroup.topEquiv : (⊤ : Subgroup F)≃*F).trans a)
    rw [card_top,hF] at hh
    omega
  have noBinaryLinear {d : ℕ} (hdd : d=4 ∨ d=5) (a : F≃*SL(d,ZMod 2)) : False := by
    rcases hdd with rfl | rfl
    · rw [Nat.card_congr a.toEquiv,Atlas.Order20160A8.sl4Two_card] at hF
      omega
    · exact ChapterC.C27Source.SmallModels.no_linearFive
        (fun S => (small S).trans (by decide)) a.symm.toMonoidHom a.symm.injective
  cases c.clause_one with
  | irreducible _ _ _ source _ =>
    cases source with
    | linearTwo K _ a _ _ =>
      have hh := linearTwo_factor_card (ρ := (ρ.comp J.subtype).comp F.subtype)
        (hf.comp (J.subtype_injective.comp F.subtype_injective))
        hd.le small (⊤ : Subgroup F) K
        ((Subgroup.topEquiv : (⊤ : Subgroup F)≃*F).trans a.groupEquiv)
      rw [card_top,hF] at hh
      omega
    | linearThree K _ a _ => exact noLinearThree K a.groupEquiv
    | symplectic K large _ a _ =>
      have hh := ChapterC.C27Source.SmallModels.symplectic_degree_eq_one
        (fun S => (small S).trans (by decide)) K a.groupEquiv.symm.toMonoidHom
        a.groupEquiv.symm.injective
      omega
    | symplecticTwo a _ =>
      exact noAlt (Or.inr (Or.inl rfl))
        (a.subgroupEquiv.trans ChapterC.C27Source.SmallModels.binarySymplecticDerivedEquiv)
    | g2 K large _ a _ _ =>
      have hh := ChapterC.C27Source.SmallModels.g2_degree_eq_one
        (fun S => (small S).trans (by decide)) K a.groupEquiv.symm.toMonoidHom
        a.groupEquiv.symm.injective
      omega
    | g2Two a _ _ =>
      rw [Nat.card_congr a.subgroupEquiv.toEquiv,
        Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hF
      omega
    | symmetric n hn a _ _ =>
      rcases hn with rfl | rfl
      · exact noAlt (Or.inl rfl) a.subgroupEquiv
      · exact not_seven_symmetric_section ρ hf hi hq A hA hfix s _ a
    | alternatingSix _ a _ _ => exact noAlt (Or.inr (Or.inl rfl)) a.groupEquiv
    | alternatingSeven _ _ _ dim _ _ =>
      change Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule)=4 at dim
      omega
    | tripleSix _ a _ =>
      have hz : Nat.card (center F)=1 := by
        rw [Nat.card_congr (centerCongr e).toEquiv,
          alternatingGroup.center_eq_bot (by simp),card_bot]
      have hthree : Nat.card (center F)=3 := by
        rw [Nat.card_congr a.centerEquiv.toEquiv]
        simp
      omega
    | binaryLinear d hdd _ a _ => exact noBinaryLinear hdd a.groupEquiv
    | orthogonalSix _ _ a _ _ => exact noAlt (Or.inr (Or.inr rfl)) a.groupEquiv
    | symmetricEight _ a _ => exact noAlt (Or.inr (Or.inr rfl)) a.subgroupEquiv
    | exteriorFive _ _ a _ _ _ => exact noBinaryLinear (Or.inr rfl) a
  | doubleThree K _ a _ _ => exact noLinearThree K a.groupEquiv
  | naturalDual d hdd _ hn =>
    obtain ⟨a⟩ := hn
    exact noBinaryLinear hdd a.groupEquiv
  | repeatedNatural d _ hdd _ _ _ hn =>
    obtain ⟨a⟩ := hn
    exact noBinaryLinear hdd a.groupEquiv

end CFSG.Quasithin.ChapterB.SourceInduction.SylowSixteenSixSpace
