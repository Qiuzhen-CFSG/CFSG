module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.TripleCover.SourceAdapter.Selection
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.TripleCover.SourceAdapter.OrdinaryAdapter
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Survivors
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions

/-!
# Actual exceptional-case consumer of the reduced source section

The source-correct projective-line and group-only outer alternatives give the
existing ExceptionalCase on the literal offender representation. Ordinary
quotients use the proved order obstruction before invoking their unchanged
local exclusions. The triple-cover branch uses only the reduced cubic-center
recovery and the actual supplied quotient equivalence.

The final adapter accepts the genuine surviving source cover rather than
silently assuming that it is the concrete hexacode group. Its comparison
parameter is explicit and belongs to qt-15-03-exceptional-coordinate-recognition
and qt-15-03-terminal-exceptional-action. This file proves neither that
comparison nor the full B.5 classification nor Theorem 15.3.1.

Source: Aschbacher--Smith, final proof of 15.3.1, printed p.1155, with
B.5.1/B.5.6, pp.99,105, and the actual covering convention of A.3.5/K.1.3.
-/

public section
open Subgroup Atlas.Codes Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.TripleCover.SourceAdapter

open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open TripleCover.GroupComparison
open Representation.Hexacode

variable {H : Type*} [Group H] [Finite H]
  {V : Subgroup H} [IsElementaryAbelian 2 (moduleClosure V)]

/-- The actual perfect cubic cover cannot embed in the first factor A6 of
an outer A6--C3 configuration. No module splitting is used. -/
theorem not_outerShape (d : SourceInput V) (e : coreQuotient H ≃* HexAutomorphisms)
    (hE : hexSign.ker ≤ d.offenderGroup.map e.toMonoidHom) :
    ¬ Nonempty (ChapterB.OuterSixThreeShape d.offenderGroup) := by
  rintro ⟨c⟩
  let K := generalizedFitting d.offenderGroup
  let : IsQuasisimple K := fitting_isQuasisimple d e hE
  let P := c.first ⊔ c.second
  let : P.Normal := outerSixThreeShape_product_normal c
  let : IsCyclic (d.offenderGroup ⧸ P) := outerSixThreeShape_quotient_isCyclic c
  have hKP : K ≤ P := le_of_isPerfect_of_solvable_quotient K P
  let g : K →* (c.first × c.second) :=
    c.product.symm.toMonoidHom.comp (Subgroup.inclusion hKP)
  have hg : Function.Injective g := c.product.symm.injective.comp
    (Subgroup.inclusion_injective hKP)
  let b : K →* Multiplicative (ZMod 3) := c.secondEquiv.toMonoidHom.comp
    ((MonoidHom.snd c.first c.second).comp g)
  let : Group.IsPerfect b.range := Group.IsPerfect.range b
  have hb (x : K) : (g x).2 = 1 := by
    apply c.secondEquiv.map_eq_one_iff.mp
    exact congrArg Subtype.val (Subsingleton.elim (⟨b x, ⟨x, rfl⟩⟩ : b.range) 1)
  have hfst : Function.Injective (fun x : K => (g x).1) := by
    intro x y he
    exact hg (Prod.ext he ((hb x).trans (hb y).symm))
  have hle := Nat.card_le_card_of_injective _ hfst
  have hKcard : Nat.card K = 1080 :=
    (Nat.card_congr (fittingEquiv d e hE).toEquiv).trans hexEven_card
  have hAcard : Nat.card c.first = 360 := by
    rw [Nat.card_congr c.firstEquiv.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  omega


/-- Extract the corrected six-clause source conclusion on the original action. -/
theorem source_quasisimple_conclusion (d : SourceInput V)
    (e : coreQuotient H ≃* HexAutomorphisms)
    (h : Intersection.SourceFFAlternative d.offenderAction) :
    Nonempty (ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction
      (generalizedFitting d.offenderGroup)) := by
  have hE := even_le_offender_image d e
  rcases h with h | ho
  · cases h with
    | trivial ht => exact (OrdinaryExclusions.not_trivial d ht).elim
    | quasisimple hq c => exact ⟨c⟩
    | symmetricThree c => exact (OrdinaryExclusions.not_symmetricThree d ⟨c⟩).elim
    | twoFactors c => exact (GroupComparison.not_twoFactors d e hE ⟨c⟩).elim
    | outerSixThree c => exact (not_outerShape d e hE ⟨c.toGroupShape⟩).elim
    | hyperplane c => exact (OrdinaryExclusions.not_hyperplane d ⟨c⟩).elim
  · exact (not_outerShape d e hE ho).elim

private theorem perfect_of_fitting_top {D : Type*} [Group D]
    (hq : IsQuasisimple (generalizedFitting D)) (ht : generalizedFitting D = ⊤) :
    Group.IsPerfect D := by
  have h := hq.toIsPerfect
  rw [ht] at h
  exact Group.IsPerfect.top_iff.mp h

private theorem perfect_map_le_even {D : Type*} [Group D] (N : Subgroup D)
    [Group.IsPerfect N] (f : D →* HexAutomorphisms) : N.map f ≤ hexSign.ker := by
  let _ : Group.IsPerfect (N.map f) := Group.IsPerfect.map f
  rw [← Representation.Hexacode.commutator_eq_even]
  conv_lhs => rw [← (N.map f).commutator_eq_self]
  exact Subgroup.commutator_mono le_top le_top

/-- The reduced section feeds the existing public ExceptionalCase directly. -/
noncomputable def exceptionalCase_of_selected (d : SourceInput V)
    (e : coreQuotient H ≃* HexAutomorphisms)
    (s : SelectedSection d.offenderAction (generalizedFitting d.offenderGroup)) :
    ExceptionalCase d := by
  have hE := even_le_offender_image d e
  have hq := GroupComparison.fitting_isQuasisimple d e hE
  let _ : Group.IsPerfect d.offenderGroup := perfect_of_fitting_top hq s.whole
  exact
    { actor := e
      offender_image := le_antisymm (perfect_map_le_even d.offenderGroup e.toMonoidHom) hE
      irreducible := s.original_isIrreducible d.offenderAction_moved_eq_top
      dimension := s.finrank_eq_six d.offenderAction_moved_eq_top }

/-- In the concrete triple-cover branch, corrected source alternatives suffice;
no legacy offender, section-selection or fixed-kernel premise remains. -/
theorem exceptionalCase_of_sourceAlternative (d : SourceInput V)
    (e : coreQuotient H ≃* HexAutomorphisms)
    (h : Intersection.SourceFFAlternative d.offenderAction) :
    Nonempty (ExceptionalCase d) := by
  obtain ⟨c⟩ := source_quasisimple_conclusion d e h
  obtain ⟨s, hs⟩ := selectedSection_of_source d.offenderAction
    (GroupComparison.fittingEquiv d e (even_le_offender_image d e)) c
  exact ⟨exceptionalCase_of_selected d e s⟩

omit [Finite H] in
/-- The actual offender subgroup order divides the full quotient order. -/
theorem offender_not1080_of_full (d : SourceInput V)
    (h : ¬ 1080 ∣ Nat.card (coreQuotient H)) :
    ¬ 1080 ∣ Nat.card d.offenderGroup :=
  fun hd => h (hd.trans d.offenderGroup.card_subgroup_dvd_card)

/-- Source-correct replacement for OrdinaryExclusions on the same four
concrete full quotients. Every unchanged ordinary-action proof is reused. -/
theorem exceptionalCase_of_four_quotients (d : SourceInput V)
    (quotient : FullQuotientAlternative (coreQuotient H))
    (h : Intersection.SourceFFAlternative d.offenderAction) :
    Nonempty (ExceptionalCase d) := by
  cases quotient with
  | symmetricSix e =>
      have hd : ¬ 1080 ∣ Nat.card (coreQuotient H) := by
        rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
        norm_num [Nat.factorial]
      exact (OrdinaryExclusions.Permutation.not_symmetric_six d
        (alternative_of_not1080 (offender_not1080_of_full d hd) h) e).elim
  | tripleSymmetricSix e => exact exceptionalCase_of_sourceAlternative d e h
  | symmetricSeven e =>
      have hd : ¬ 1080 ∣ Nat.card (coreQuotient H) := by
        rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
        norm_num [Nat.factorial]
      exact (OrdinaryExclusions.Permutation.not_symmetric_seven d
        (alternative_of_not1080 (offender_not1080_of_full d hd) h) e).elim
  | g2Two e =>
      have hd : ¬ 1080 ∣ Nat.card (coreQuotient H) := by
        rw [Nat.card_congr e.toEquiv, Atlas.G2.card_Model, Nat.card_zmod]
        norm_num
      exact (OrdinaryExclusions.not_g2 d
        (alternative_of_not1080 (offender_not1080_of_full d hd) h) e).elim

/-- The source-facing consumer retains the exact missing cover comparison.
No Sylow, residual, action, or local-source field of d is replaced. -/
theorem exceptionalCase_of_surviving_source (d : SourceInput V)
    (quotient : Cases.SurvivingQuotientAlternative (coreQuotient H))
    (h : Intersection.SourceFFAlternative d.offenderAction)
    (coverComparison : FSource.TripleSymmetric (coreQuotient H) 6 →
      Nonempty (coreQuotient H ≃* HexAutomorphisms)) :
    Nonempty (ExceptionalCase d) := by
  apply exceptionalCase_of_four_quotients d ?_ h
  cases quotient with
  | symmetricSix e => exact .symmetricSix e
  | tripleSymmetricSix c =>
      obtain ⟨e⟩ := coverComparison c
      exact .tripleSymmetricSix e
  | symmetricSeven e => exact .symmetricSeven e
  | g2Two e => exact .g2Two e

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.TripleCover.SourceAdapter
