module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Reduction
public import Theory.Representation.HexacodeAction.TerminalIrreducible
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.TripleCover.Recovery
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.TripleCover.GroupComparison
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.TripleCover.ActionSelection
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.ExceptionalCase

/-!
# The even offender group and original module in the terminal triple cover

The ordinary exclusions retain the actual offender-generated subgroup and
prove that its quotient in the full actor is a two-group. Under an actor
equivalence with the concrete full hexacode automorphism group, the perfect
even cover therefore lies in the actual image of the offender group. The
group comparison identifies its generalized Fitting subgroup with that
cover and excludes the product and outer-six-three alternatives.

The action comparison then selects the triple-six branch and proves that
the component is the whole offender actor. Perfectness excludes the odd
coset, and the central cubic norm recovers the original module from its
literal moved central section, including nonsplit extensions and fixed
summands. `tripleCover_conclusions` proves equality of the offender image
with the even cover, irreducibility and dimension six from just the source
input, actor equivalence and explicit classification alternative.
`exceptionalCase_of_tripleCover` packages these conclusions for recognition,
retaining the supplied actor equivalence.

This is a conditional comparison, not a proof of the universal B.5.6
classification. In particular it does not certify the legacy offender-line
clause of `TripleSixAction`; recovery uses only its cubic center and
dimension. Construction of the classification input remains upstream.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.5.1,
B.5.6 and the final proof of 15.3.1, printed pp.99, 105 and 1155; the
triple-cover convention is A.3.5 and K.1.3.
-/

@[expose] public section

open Subgroup Atlas.Codes Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition

variable {H : Type*} [Group H] [Finite H]
  {V : Subgroup H} [IsElementaryAbelian 2 (moduleClosure V)]

/-- The perfect even hexacode cover is forced into the actual offender image.

The image is normal because the offender group is normal in the core
quotient.  Its quotient in the full hexacode automorphism group is a
two-group by transport of the source quotient clause.  A nontrivial image of
the perfect even cover in that nilpotent quotient is impossible, so every
even automorphism lies in the offender image.
-/
theorem even_le_offender_image (d : SourceInput V)
    (e : coreQuotient H ≃* HexAutomorphisms) :
    hexSign.ker ≤ d.offenderGroup.map e.toMonoidHom := by
  let N : Subgroup (coreQuotient H) := d.offenderGroup
  let N' : Subgroup HexAutomorphisms := N.map e.toMonoidHom
  let _ : N'.Normal := d.offenderGroup_normal.map e.toMonoidHom e.surjective
  let qN : HexAutomorphisms →* HexAutomorphisms ⧸ N' := QuotientGroup.mk' N'
  let eqv : (coreQuotient H ⧸ N) ≃* (HexAutomorphisms ⧸ N') :=
    QuotientGroup.congr N N' e (by rfl)
  have hq : IsPGroup 2 (HexAutomorphisms ⧸ N') :=
    (d.quotient_offenderGroup_isTwoGroup.of_equiv eqv)
  let f : HexEvenAutomorphisms →* (HexAutomorphisms ⧸ N') :=
    qN.comp hexSign.ker.subtype
  let _ : Group.IsPerfect HexEvenAutomorphisms :=
    Representation.Hexacode.even_isPerfect
  let _ : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hrange : f.range = ⊥ := by
    by_contra hn
    let _ : Nontrivial f.range := (Subgroup.nontrivial_iff_ne_bot f.range).mpr hn
    exact Group.IsPerfect.not_isNilpotent f.range (hq.to_subgroup f.range).isNilpotent
  intro x hx
  let xe : HexEvenAutomorphisms := ⟨x, hx⟩
  have hxe : f xe ∈ (⊥ : Subgroup (HexAutomorphisms ⧸ N')) := by
    rw [← hrange]
    exact ⟨xe, rfl⟩
  have hqone : qN (hexSign.ker.subtype xe) = 1 :=
    (Subgroup.mem_bot.mp hxe)
  have hker : hexSign.ker.subtype xe ∈ qN.ker :=
    (MonoidHom.mem_ker.mpr hqone)
  have hmem : hexSign.ker.subtype xe ∈ N' := by
    rwa [QuotientGroup.ker_mk'] at hker
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmem
  apply Subgroup.mem_map.mpr
  refine ⟨y, hy, ?_⟩
  simpa [xe] using hyeq

/-- The only remaining possibilities for the actual offender image are the
even cover and the full hexacode automorphism group. -/
theorem offender_image_eq_even_or_top (d : SourceInput V)
    (e : coreQuotient H ≃* HexAutomorphisms) :
    d.offenderGroup.map e.toMonoidHom = hexSign.ker ∨
      d.offenderGroup.map e.toMonoidHom = ⊤ := by
  let N : Subgroup HexAutomorphisms := d.offenderGroup.map e.toMonoidHom
  have hE : hexSign.ker ≤ N := even_le_offender_image d e
  by_cases hN : N ≤ hexSign.ker
  · exact Or.inl (le_antisymm hN hE)
  · have ⟨x, hxN, hxodd⟩ : ∃ x : HexAutomorphisms, x ∈ N ∧ hexSign x ≠ 1 := by
      by_contra hn
      push Not at hn
      exact hN (by
        intro x hx
        exact (hexSign.mem_ker.mpr (hn x hx)))
    have hxminus : hexSign x = -1 := by
      rcases Int.units_eq_one_or (hexSign x) with hxone | hxminus
      · exact (hxodd hxone).elim
      · exact hxminus
    apply Or.inr
    apply top_unique
    intro g hg
    rcases Int.units_eq_one_or (hexSign g) with hg1 | hgminus
    · exact hE (hexSign.mem_ker.mp hg1)
    · have hxe : x⁻¹ * g ∈ hexSign.ker := by
        apply hexSign.mem_ker.mpr
        simp only [map_mul, map_inv]
        rw [hxminus, hgminus]
        simp
      have hxin : x⁻¹ * g ∈ N := hE hxe
      exact (mul_inv_cancel_left x g) ▸ N.mul_mem hxN hxin

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

/-- Once B.5.1 selects the triple-six component as the whole offender actor,
perfectness excludes every odd element from the actual offender image.
Branch selection remains an explicit premise of this conditional deduction. -/
theorem offender_image_eq_even_of_selected (d : SourceInput V)
    (e : coreQuotient H ≃* HexAutomorphisms)
    (hq : IsQuasisimple (generalizedFitting d.offenderGroup))
    (s : TripleCover.SelectedSection d.offenderAction (generalizedFitting d.offenderGroup)) :
    d.offenderGroup.map e.toMonoidHom = hexSign.ker := by
  let _ : Group.IsPerfect d.offenderGroup := perfect_of_fitting_top hq s.whole
  exact le_antisymm (perfect_map_le_even d.offenderGroup e.toMonoidHom)
    (even_le_offender_image d e)

/-- The literal source module recovers the selected irreducible section and
its six dimensions. Together with perfectness this supplies the consumer's
exceptional witness, conditional on the still-required branch selection. -/
noncomputable def exceptionalCase_of_selected (d : SourceInput V)
    (e : coreQuotient H ≃* HexAutomorphisms)
    (hq : IsQuasisimple (generalizedFitting d.offenderGroup))
    (s : TripleCover.SelectedSection d.offenderAction (generalizedFitting d.offenderGroup)) :
    ExceptionalCase d where
  actor := e
  offender_image := offender_image_eq_even_of_selected d e hq s
  irreducible := s.original_isIrreducible d.offenderAction_moved_eq_top
  dimension := s.finrank_eq_six d.offenderAction_moved_eq_top

namespace TripleCover

/-- The intrinsic group comparison selects the exact section in any supplied
B.5.1 conclusion, without a separate component-isomorphism premise. -/
theorem selectedSection_of_conclusion (d : SourceInput V)
    (e : coreQuotient H ≃* HexAutomorphisms)
    (c : QuasisimpleSourceConclusion d.offenderAction
      (generalizedFitting d.offenderGroup)) :
    ∃ s : SelectedSection d.offenderAction (generalizedFitting d.offenderGroup),
      s.sectionData = c.sectionData :=
  selectedSection_of_offender d
    (GroupComparison.fittingEquiv d e (even_le_offender_image d e)) c

/-- Every other source branch has been excluded. The surviving section is
faithful, irreducible, and triple-six, and its component is the whole actor. -/
theorem selectedSection_of_alternative (d : SourceInput V)
    (e : coreQuotient H ≃* HexAutomorphisms)
    (h : SourceAlternative d.offenderAction) :
    Nonempty (SelectedSection d.offenderAction (generalizedFitting d.offenderGroup)) := by
  obtain ⟨c⟩ := GroupComparison.quasisimple_source_conclusion d e h
    (even_le_offender_image d e)
  obtain ⟨s, _⟩ := selectedSection_of_conclusion d e c
  exact ⟨s⟩

/-- For the literal source section, the moved space is the original module
and its fixed kernel is zero. Neither splitting nor absence of a fixed
summand is an additional premise. -/
theorem source_section_recovery (d : SourceInput V)
    (e : coreQuotient H ≃* HexAutomorphisms)
    (c : QuasisimpleSourceConclusion d.offenderAction
      (generalizedFitting d.offenderGroup)) :
    c.sectionData.space.toSubmodule = ⊤ ∧
      c.sectionData.central.toSubmodule = ⊥ := by
  obtain ⟨s, hs⟩ := selectedSection_of_conclusion d e c
  rw [← hs]
  exact ⟨s.space_eq_top d.offenderAction_moved_eq_top,
    s.central_eq_bot d.offenderAction_moved_eq_top⟩

/-- The actual central projection identifies the original representation
with the section action, preserving every offender-group element. -/
theorem source_section_repEquiv (d : SourceInput V)
    (e : coreQuotient H ≃* HexAutomorphisms)
    (c : QuasisimpleSourceConclusion d.offenderAction
      (generalizedFitting d.offenderGroup)) :
    Nonempty (Representation.RepEquiv d.offenderAction c.sectionData.action) := by
  obtain ⟨s, hs⟩ := selectedSection_of_conclusion d e c
  rw [← hs]
  exact ⟨⟨s.originalEquiv d.offenderAction_moved_eq_top,
    fun g => LinearMap.ext (s.projection_intertwines d.offenderAction_moved_eq_top g)⟩⟩

end TripleCover

/-- The complete triple-cover comparison from the stated source inputs.
The even-cover containment, component identification, action selection and
recovery of the original module are all discharged here. The image uses the
supplied equivalence, and both module conclusions concern the original
conjugate span, before passing to any central section. -/
theorem tripleCover_conclusions (d : SourceInput V)
    (e : coreQuotient H ≃* HexAutomorphisms)
    (h : SourceAlternative d.offenderAction) :
    d.offenderGroup.map e.toMonoidHom = hexSign.ker ∧
      Representation.IsIrreducible d.offenderAction ∧
      Module.finrank (ZMod 2) (Additive (moduleClosure V)) = 6 := by
  obtain ⟨s⟩ := TripleCover.selectedSection_of_alternative d e h
  have hq := TripleCover.GroupComparison.fitting_isQuasisimple d e
    (even_le_offender_image d e)
  exact ⟨offender_image_eq_even_of_selected d e hq s,
    s.original_isIrreducible d.offenderAction_moved_eq_top,
    s.finrank_eq_six d.offenderAction_moved_eq_top⟩

/-- The proved triple-cover conclusions supply the intermediate recognition
witness, with no extra branch-selection or section-recovery premise. -/
noncomputable def exceptionalCase_of_tripleCover (d : SourceInput V)
    (e : coreQuotient H ≃* HexAutomorphisms)
    (h : SourceAlternative d.offenderAction) : ExceptionalCase d where
  actor := e
  offender_image := (tripleCover_conclusions d e h).1
  irreducible := (tripleCover_conclusions d e h).2.1
  dimension := (tripleCover_conclusions d e h).2.2

/-- Packaging the conclusions preserves the caller's particular actor
equivalence, rather than choosing a new identification of the quotient. -/
@[simp] theorem exceptionalCase_of_tripleCover_actor (d : SourceInput V)
    (e : coreQuotient H ≃* HexAutomorphisms)
    (h : SourceAlternative d.offenderAction) :
    (exceptionalCase_of_tripleCover d e h).actor = e := rfl

/-- The given actor equivalence maps precisely the offender group onto the
even cover; there is no remaining branch-selection hypothesis. -/
theorem offender_image_eq_even (d : SourceInput V)
    (e : coreQuotient H ≃* HexAutomorphisms)
    (h : SourceAlternative d.offenderAction) :
    d.offenderGroup.map e.toMonoidHom = hexSign.ker :=
  (exceptionalCase_of_tripleCover d e h).offender_image

/-- The full odd-coset offender image is impossible in the triple-cover
branch. The even and full concrete covers have different orders. -/
theorem offender_image_ne_top (d : SourceInput V)
    (e : coreQuotient H ≃* HexAutomorphisms)
    (h : SourceAlternative d.offenderAction) :
    d.offenderGroup.map e.toMonoidHom ≠ ⊤ := by
  rw [offender_image_eq_even d e h]
  intro ht
  have hc := hexEven_card
  change Nat.card hexSign.ker = 1080 at hc
  rw [ht, Subgroup.card_top, hexAutomorphisms_card] at hc
  norm_num at hc

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition
