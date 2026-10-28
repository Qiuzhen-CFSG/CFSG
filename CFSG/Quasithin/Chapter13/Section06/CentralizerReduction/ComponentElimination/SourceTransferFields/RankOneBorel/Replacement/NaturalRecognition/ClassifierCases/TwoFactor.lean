module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases.TwoFactor.Placement
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases.TwoFactor.Sections

/-!
# The rank-one component in B.5.6(3)

The marked component belongs to one literal factor. Its natural SL₂ or marked
A₅ action on the source quotient summand is compared with the literal central
quotient of its moved section. The comparison uses the kernel on that moved
space, without assuming that either ambient fixed space vanishes or that the
two fixed spaces agree. In the A₅ row, vanishing of cohomology of the natural
module and its dual splits the moved space and retains its Irr⁺ membership.
The SL₂ row transports matrix and vector coordinates to the supplied field.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.6(3),
printed p.105, and the first paragraph of 13.6.18, p.931 (PDF p.948).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Matrix
open Representation.OneCohomology
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases.TwoFactor
open ChapterB.QuasisimpleSource ChapterB.SourceInduction ChapterB.QuasisimpleSource.ExtensionConsequences

variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {C A : Subgroup D}

private theorem alternating_invariants : Representation.invariants (alternatingNatural 5) = ⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact invariants_eq_bot_of_faithful_irreducible _
    ((BinaryPermutation.naturalRepresentation_injective (Ω := Fin 5) (by decide)).comp
      (alternatingGroup (Fin 5)).subtype_injective)
    (BinaryPermutation.alternatingNatural_isIrreducible (Ω := Fin 5) (by decide))

private theorem alternating_split [Module.Finite (ZMod 2) V]
    (s : MovedSection ρ C) (hi : IsIrrPlus ρ C s.space.toSubmodule)
    (e : ActionEquiv (s.action.comp C.subtype) (alternatingNatural 5)) :
    IsCompl s.space.toSubmodule (fixedSpace ρ C) := by
  let : Subsingleton (H1 (alternatingNatural 5)) := by
    apply (Module.finrank_zero_iff (R := ZMod 2)).mp
    exact BinaryPermutation.alternatingNatural_finrank_H1_eq_zero_of_odd
      (Fin 5) (by simp) (by simpa using (show Odd 5 by decide))
  let sd : ActionEquiv (alternatingNatural 5) (Representation.dual (alternatingNatural 5)) :=
    ⟨MulEquiv.refl _, BinaryPermutation.naturalDualEquiv (Fin 5),
      fun g v => BinaryPermutation.naturalDualEquiv_equivariant (Fin 5) g.val v⟩
  let : Subsingleton (H1 (Representation.dual (alternatingNatural 5))) :=
    (actionSymm sd).H1_subsingleton
  exact moved_isCompl_of_equiv s hi e

/-- A factor containing the marked component supplies the required coordinates
on its literal moved section, including the whole-space A₅ splitting. -/
theorem component_case_of_le [C.Normal] [Module.Finite (ZMod 2) V]
    (hC : IsQuasisimple C) (hCA : C ≤ A)
    (F : BinaryField) (hF : 1 < F.degree) (e : C ≃* SL(2,F.Carrier))
    (U : Subrepresentation ρ) (h : SourceFactorCase ρ A U) :
    RankOneComponentCase ρ C F := by
  let := hC
  obtain ⟨hle,ha⟩ := factor_action ⟨(inferInstance : C.Normal).isSubnormal,hC⟩ hCA F hF e U h
  let s := MovedSection.ofNormal ρ C
  cases ha with
  | natural E a =>
    let t := modelSectionAction s U hle a (linearNatural_irreducible E (by decide))
      (linearNatural_invariants E (by decide))
    exact .natural s (FactorExtraction.transAction t
      (sameFieldNatural E F (a.groupEquiv.symm.trans e)))
  | alternatingFive a =>
    let t := modelSectionAction s U hle a
      (BinaryPermutation.alternatingNatural_isIrreducible (Ω := Fin 5) (by decide))
      alternating_invariants
    have hi := section_irrPlus s (irreducible_of_equiv t
      (BinaryPermutation.alternatingNatural_isIrreducible (Ω := Fin 5) (by decide)))
    have hc := alternating_split s hi t
    exact .alternatingFive s hi (FactorExtraction.transAction
      (FactorExtraction.movedActionOfCentralBot s (disjoint_iff.mp hc.disjoint)) t)

/-- The complete rank-one component specialization of the native two-factor
branch. Both literal factors and all source constructors are covered. -/
theorem component_case {𝒦 : GroupClass} (hyp : FFHypothesis 𝒦 ρ)
    [C.Normal] (hC : IsQuasisimple C)
    (F : BinaryField) (hF : 1 < F.degree) (e : C ≃* SL(2,F.Carrier))
    (c : SourceTwoFactorCase ρ) : RankOneComponentCase ρ C F := by
  let := hyp.finite_module
  rcases component_le_factor ⟨(inferInstance : C.Normal).isSubnormal,hC⟩ c.product with h | h
  · exact component_case_of_le hC h F hF e c.firstSpace c.firstCase
  · exact component_case_of_le hC h F hF e c.secondSpace c.secondCase
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases.TwoFactor
