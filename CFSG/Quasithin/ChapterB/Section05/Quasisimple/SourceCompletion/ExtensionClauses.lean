module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.OuterComplement
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.SymplecticTwo
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.DualExtensions
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.DualExtensions.BinaryTrace
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.DualExtensions.NonbinaryTrace
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ParabolicConclusion

/-!
# All extension conclusions of B.5.1 with the source projective-line convention

The corrected triple-cover row splits by central-element cohomology; its
ratio-one equality also identifies the component-fixed and whole-group-fixed
spaces. Every other row retains precisely the existing action data, allowing
the proved cohomology, binary symplectic comparison, and outer-complement
arguments to supply clauses (2)--(5). Clause (6) uses the literal moved-module
Sylow calculation. No incorrect one-dimensional offender clause is constructed.

The sole extra earlier-source input below is the explicit nonbinary G₂
best-offender root-pair placement from B.4.6(13). It excludes the dual G₂
extension in clause (5); all other extension arguments have been proved.
The B.5.1 action alternative itself must still be established by its owner.

Source: Aschbacher--Smith, combined manuscript, B.5.1, pp.99 and 102--103;
B.4.6(13), pp.89--90; K.1.3, p.453.
-/

public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
open ExtensionConsequences
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The concrete earlier G₂ placement needed only over nonbinary fields. -/
@[expose] def NonbinaryG2RootPairInput : Prop :=
  ∀ F : BinaryField, 1 < F.degree → DualExtensions.G2BestOffenderRootPair F

private theorem catalogue_legacy_or_triple {L H : Subgroup G}
    (hc : SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H) :
    IrreducibleActionCase ρ L H ∨
      (Nonempty (center L ≃* Multiplicative (ZMod 3)) ∧ quadraticRatio ρ = 1) := by
  cases hc with
  | linearTwo F hg e ho hq => exact Or.inl (.linearTwo F hg e ho hq)
  | linearThree F hg e hq => exact Or.inl (.linearThree F hg e hq)
  | symplectic F hd hg e hq => exact Or.inl (.symplectic F hd hg e hq)
  | symplecticTwo e hq => exact Or.inl (.symplecticTwo e hq)
  | g2 F hd hg e ho hq => exact Or.inl (.g2 F hd hg e ho hq)
  | g2Two e ho hq => exact Or.inl (.g2Two e ho hq)
  | symmetric n hn e ho hq => exact Or.inl (.symmetric n hn e ho hq)
  | alternatingSix hg e ho hq => exact Or.inl (.alternatingSix hg e ho hq)
  | alternatingSeven hg hw e hd ho hq => exact Or.inl (.alternatingSeven hg hw e hd ho hq)
  | tripleSix _ a hq => exact Or.inr ⟨⟨a.centerEquiv⟩, hq⟩
  | binaryLinear d hd hg e hq => exact Or.inl (.binaryLinear d hd hg e hq)
  | orthogonalSix hg hw e ho hq => exact Or.inl (.orthogonalSix hg hw e ho hq)
  | symmetricEight hw e hq => exact Or.inl (.symmetricEight hw e hq)
  | exteriorFive hg hw e hd ho hq => exact Or.inl (.exteriorFive hg hw e hd ho hq)

private theorem irreducible_dual [FiniteDimensional (ZMod 2) V]
    [IsIrreducible ρ] : IsIrreducible ρ.dual := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  refine ⟨fun W => ?_⟩
  let U : Subrepresentation ρ :=
    { toSubmodule := W.toSubmodule.dualCoannihilator
      apply_mem_toSubmodule g v hv := by
        rw [Submodule.mem_dualCoannihilator] at hv ⊢
        intro f hf
        have h := hv (ρ.dual g⁻¹ f) (W.apply_mem_toSubmodule g⁻¹ hf)
        simpa only [dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, inv_inv] using h }
  have hd : U.toSubmodule.dualAnnihilator = W.toSubmodule :=
    Subspace.dualCoannihilator_dualAnnihilator_eq
  rcases eq_bot_or_eq_top U with h | h
  · right
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, h]
    exact Submodule.dualAnnihilator_bot
  · left
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, h]
    exact Submodule.dualAnnihilator_top

private theorem faithful_dual (hf : Function.Injective ρ) : Function.Injective ρ.dual := by
  intro g h he
  apply inv_injective
  apply hf
  ext v
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp
  intro f
  have hh := congrArg (fun t : Module.End (ZMod 2) (Module.Dual (ZMod 2) V) => t f v) he
  change f (ρ g⁻¹ v) = f (ρ h⁻¹ v) at hh
  simpa only [map_sub] using sub_eq_zero.mpr hh

private theorem central_isCompl [Finite G] [FiniteDimensional (ZMod 2) V]
    {L : Subgroup G} (s : MovedSection ρ L)
    (hi : IsIrrPlus ρ L s.space.toSubmodule) (hf : Function.Injective s.action)
    (hirr : IsIrreducible (s.action.comp L.subtype))
    (e : center L ≃* Multiplicative (ZMod 3)) :
    IsCompl s.space.toSubmodule (fixedSpace ρ L) := by
  let z := e.symm (Multiplicative.ofAdd (1 : ZMod 3))
  have hzn : z.val ≠ 1 := by
    intro hz
    have he : e z = 1 := by rw [show z = 1 from Subtype.ext hz, map_one]
    have hz' : Multiplicative.ofAdd (1 : ZMod 3) = 1 :=
      (e.apply_symm_apply _).symm.trans he
    exact one_ne_zero (show (1 : ZMod 3) = 0 from hz')
  let := hirr
  have hfL : Function.Injective (s.action.comp L.subtype) := hf.comp Subtype.val_injective
  let := subsingleton_H1_of_faithful_irreducible_central _ hfL z.val z.property hzn
  let := irreducible_dual (ρ := s.action.comp L.subtype)
  let := subsingleton_H1_of_faithful_irreducible_central _ (faithful_dual hfL)
    z.val z.property hzn
  exact moved_isCompl_of_cohomology s hi

/-- The corrected action list gives either the unchanged legacy data or a
proved splitting in its corrected triple-cover row. This is not a conversion
of the two incompatible offender conventions. -/
theorem action_legacy_or_split [Finite G] {K : GroupClass.{u}} {L : Subgroup G}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hc : SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s) :
    QuasisimpleActionCase ρ L s ∨
      (IsCompl s.space.toSubmodule (fixedSpace ρ L) ∧
        IsCompl s.space.toSubmodule ρ.invariants) := by
  let := h.finite_module
  cases hc with
  | irreducible hi hf hirr hs he =>
    rcases catalogue_legacy_or_triple hs with hs | ⟨⟨e⟩, hq⟩
    · exact Or.inl (.irreducible hi hf hirr hs he)
    · let := h.quasisimple
      let := component_normal_of_fitting_eq_sup_center L h.fitting
      have hcomp := central_isCompl s hi hf hirr e
      exact Or.inr ⟨hcomp, (DualExtensions.fixed_eq_invariants s hq h.generated) ▸ hcomp⟩
  | doubleThree F hw e ho hq => exact Or.inl (.doubleThree F hw e ho hq)
  | naturalDual d hd hw hn => exact Or.inl (.naturalDual d hd hw hn)
  | repeatedNatural d r hd hr hb hw hn => exact Or.inl (.repeatedNatural d r hd hr hb hw hn)

/-- B.5.1(2), retaining the natural model and the literal moved quotient. -/
theorem clause_two [Finite G] {K : GroupClass.{u}} {L : Subgroup G}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hc : SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s)
    (hn : ¬ IsCompl s.space.toSubmodule (fixedSpace ρ L)) :
    IsIrrPlus ρ L s.space.toSubmodule ∧ NonsplitNatural (s.action.comp L.subtype) := by
  rcases action_legacy_or_split h s hc with hc | hs
  · have hi := irreducible_of_not_compl_fixed h s hc hn
    refine ⟨hi.irrPlus, ?_⟩
    rcases nonsplitNatural_or_symplecticTwo h s hi hn with hnature | ⟨e⟩
    · exact hnature
    · obtain ⟨e⟩ := e
      exact .alternatingSix ⟨⟨e.groupEquiv.trans SymplecticTwo.derivedNaturalActionEquiv.groupEquiv,
        e.linearEquiv.trans SymplecticTwo.derivedNaturalActionEquiv.linearEquiv,
        fun g v => (congrArg SymplecticTwo.derivedNaturalActionEquiv.linearEquiv
          (e.intertwines g v)).trans (SymplecticTwo.derivedNaturalActionEquiv.intertwines _ _)⟩⟩
  · exact False.elim (hn hs.1)

/-- B.5.1(3), with the sole natural-plus-dual exception. -/
theorem clause_three {L : Subgroup G} (s : MovedSection ρ L)
    (hc : SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s) :
    IsHomogeneousAction (s.action.comp L.subtype) ∨
      ∃ d, (d = 4 ∨ d = 5) ∧
        IsNaturalPlusDual (s.space.toRepresentation.comp L.subtype) d := by
  cases hc with
  | irreducible _ _ hi _ _ => exact Or.inl (homogeneous_of_irreducible hi)
  | doubleThree F _ e _ _ =>
    exact Or.inl (homogeneous_moved_quotient s F (by decide) (by decide) e)
  | naturalDual d hd _ hn => exact Or.inr ⟨d, hd, hn⟩
  | repeatedNatural d r hd hr _ _ hn =>
    obtain ⟨e⟩ := hn
    exact Or.inl (homogeneous_moved_quotient s BinaryField.two
      (by rcases hd with rfl | rfl <;> decide) hr e)

/-- B.5.1(4), including the order-two quotient of the actual fixed spaces. -/
theorem clause_four [Finite G] {K : GroupClass.{u}} {L : Subgroup G}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hc : SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s)
    (hn : ¬ IsCompl s.space.toSubmodule ρ.invariants) :
    IsIrrPlus ρ L s.space.toSubmodule ∧
      (¬ IsCompl s.space.toSubmodule (fixedSpace ρ L) ∨
        (IsCompl s.space.toSubmodule (fixedSpace ρ L) ∧
          (IsSymmetricNatural s.space.toRepresentation 6 ∨
            IsSymmetricNatural s.space.toRepresentation 8) ∧
          Nat.card ((fixedSpace ρ L) ⧸
            ρ.invariants.comap (fixedSpace ρ L).subtype) = 2)) := by
  classical
  rcases action_legacy_or_split h s hc with hc | hs
  · have hi := irreducible_of_not_compl_invariants h s hc hn
    refine ⟨hi.irrPlus, ?_⟩
    by_cases hcomp : IsCompl s.space.toSubmodule (fixedSpace ρ L)
    · have he := outer_complement h s hi hcomp hn
      exact Or.inr ⟨hcomp, he.1, he.2.1⟩
    · exact Or.inl hcomp
  · exact False.elim (hn hs.2)

private theorem legacy_supplement_natural [Finite G] {K : GroupClass.{u}}
    {L : Subgroup G} (hroot : NonbinaryG2RootPairInput)
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hi : IrreducibleAlternative L s)
    (hn : s.space.toSubmodule ⊔ ρ.invariants ≠ ⊤) :
    SupplementNatural (s.action.comp L.subtype) := by
  classical
  let := h.finite_module
  have hnG : ¬ IsCompl s.space.toSubmodule ρ.invariants :=
    fun hc => hn (codisjoint_iff.mp hc.codisjoint)
  by_cases hcomp : IsCompl s.space.toSubmodule (fixedSpace ρ L)
  · rcases (outer_complement h s hi hcomp hnG).2.2 with ha | ha
    · exact .alternatingSix ha
    · exact .alternatingEight ha
  cases hi.source with
  | linearTwo _ hg _ hoff hq =>
    exact False.elim (linearTwo_excluded h s hn hg hoff hq)
  | linearThree F _ e _ =>
    by_cases hF : 1 < F.degree
    · exact False.elim (hcomp (linearThree_large_isCompl s hi.irrPlus F hF e))
    · have he : F.degree = 1 := by have hp := F.degree_pos; omega
      let q := degreeOneNaturalEquiv F he 3
      exact .linearThree ⟨⟨e.groupEquiv.trans q.groupEquiv,
        e.linearEquiv.trans q.linearEquiv,
        fun g v => (congrArg q.linearEquiv (e.intertwines g v)).trans (q.intertwines _ _)⟩⟩
  | symplectic F _ _ e _ => exact .symplectic F ⟨e⟩
  | symplecticTwo e _ => exact .alternatingSix (SymplecticTwo.marked_isAlternatingNatural e)
  | g2 F hF hg e hoff hq =>
    exact False.elim (hn (DualExtensions.g2_supplement_of_bestOffender_rootPair
      h s F hg e hoff hq (hroot F hF)))
  | g2Two e hoff hq => exact False.elim (hn (DualExtensions.g2Two_supplement h s e hoff hq))
  | symmetric n hn' e _ _ => exact False.elim (hcomp (symmetricOdd_isCompl s hi.irrPlus hn' e))
  | alternatingSix _ e _ _ => exact .alternatingSix ⟨e⟩
  | alternatingSeven _ _ e hd _ _ => exact False.elim (hcomp (alternatingSeven_isCompl s hi e hd))
  | tripleSix _ a _ => exact False.elim (hcomp (tripleSix_isCompl s hi a))
  | binaryLinear d hd _ e _ =>
    exact False.elim (hcomp (binaryLinear_isCompl s hi.irrPlus
      (by rcases hd with rfl | rfl <;> decide) e))
  | orthogonalSix _ _ e _ _ => exact .alternatingEight ⟨e⟩
  | symmetricEight _ e _ => exact .alternatingEight ⟨markedRestriction e⟩
  | exteriorFive _ _ e hd _ _ => exact False.elim (hcomp (exteriorFive_isCompl s hi e hd))

/-- B.5.1(5). The only additional source datum is the explicit nonbinary G₂
root placement; the binary G₂, SL₂ and L₃(2) kernel arguments are discharged. -/
theorem clause_five [Finite G] {K : GroupClass.{u}} {L : Subgroup G}
    (hroot : NonbinaryG2RootPairInput)
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hc : SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s) :
    s.space.toSubmodule ⊔ ρ.invariants = ⊤ ∨
      (IsIrrPlus ρ L s.space.toSubmodule ∧
        SupplementNatural (s.action.comp L.subtype) ∧
        (Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) →
          s.space.toSubmodule ⊓ fixedSpace ρ L = ⊥)) := by
  classical
  by_cases hn : s.space.toSubmodule ⊔ ρ.invariants = ⊤
  · exact Or.inl hn
  right
  rcases action_legacy_or_split h s hc with hc | hs
  · have hi := irreducible_of_no_supplement h s hc hn
    exact ⟨hi.irrPlus, legacy_supplement_natural hroot h s hi hn,
      fun he => linearThree_fixed_kernel h s (linearThree_eq_top h s hi he) he hn⟩
  · exact False.elim (hn (codisjoint_iff.mp hs.2.codisjoint))

/-- Assemble all six source conclusions on the original representation from
its proved action alternative. The induction owner must supply that alternative
and its Fitting equality; this theorem supplies every subsequent conclusion. -/
noncomputable def conclusion_of_action [Finite G] {K : GroupClass.{u}} {L : Subgroup G}
    (hroot : NonbinaryG2RootPairInput)
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hfit : L = Theory.GroupTheory.generalizedFitting G)
    (hc : SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s) : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ L := by
  let := h.finite_module
  exact {
    sectionData := s
    fitting_eq := hfit
    clause_one := hc
    nonsplitting_iff := nonsplitting_iff ρ L s
    clause_two := clause_two h s hc
    clause_three := clause_three s hc
    clause_four := clause_four h s hc
    clause_five := clause_five hroot h s hc
    clause_six := fun _ hd hL hn T => s.sylowFixedCentralizer_of_naturalDual ρ hd hL hn T }

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
