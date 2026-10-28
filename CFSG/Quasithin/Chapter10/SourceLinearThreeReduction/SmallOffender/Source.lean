module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Preparation
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.MovedSize
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.FieldFour

/-!
# Assembly of the two independent small-offender steps

Recognition supplies a contained reselected natural linear-three module or
an actual SL₂(4) quotient. The exceptional isomorphism excludes the latter.
Minimality preserves the full module and the original offender. The separate
natural corank-one contradiction then forces its integer corank to be at
least two, hence w≥2 by attainment.

The two source arguments remain explicit inputs and have independent proof
owners. This conditional assembly does not prove either argument or the
unconditional `SourceNonnormalSmallOffenderAt`. Its exact result is the hsmall
input to `source_nonnormalReduction_of_point_generation_smallOffender`.

Source: Aschbacher--Smith, 10.2.12, printed pp.754--755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender
open Chapter3.Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {g : G}

/-- Recognition and the natural small-corank exclusion yield the literal
survivor, preserving the full module on which point control was established. -/
theorem Configuration.survivor_of_source_steps
    (c : Configuration T D g) (hrecognition : RecognitionAt T)
    (hexclusion : NaturalSmallCorankExclusionAt T) :
    ∃ E : FundamentalSetup KnownSimple.IsKnownSimple T L,
      E.fullModule = D.fullModule ∧ Nonempty (SourceLinearThreeGeometry T E) ∧
      2 ≤ globalW E.fullModule (T : Subgroup G) := by
  rcases hrecognition L D g c with hfour | ⟨E,hE,⟨m⟩⟩
  · exact (not_slTwo_of_not_alternatingFive c.notA5
      (GaloisField.card 2 2 (by decide)) hfour).elim
  · obtain ⟨he,cE⟩ := c.reselect E hE
    refine ⟨E,he,⟨m⟩,?_⟩
    have hk : 2 ≤ subgroupCorank (E.fullModule.map (MulAut.conj g).toMonoidHom)
        (E.fullModule.map (MulAut.conj g).toMonoidHom ⊓ E.maximalLocal) := by
      by_contra hlt
      exact hexclusion L E g cE m (by omega)
    rw [cE.attained]
    exact_mod_cast hk

/-- The exact published conditional contract, with two owned earlier source
steps still explicit. Final discharge remains in this module's task. -/
theorem source_nonnormalSmallOffender_of_source_steps
    (hrecognition : RecognitionAt T) (hexclusion : NaturalSmallCorankExclusionAt T) :
    SourceNonnormalSmallOffenderAt T := by
  intro hmany L D hmin hn hnotA5 hcent g hg hcomm hw hsmall
  let c : Configuration T D g :=
    ⟨hmany,hmin,hn,hnotA5,hcent,hg,hcomm,hw,hsmall⟩
  exact c.survivor_of_source_steps hrecognition hexclusion

end CFSG.Quasithin.Chapter10.SmallOffender
