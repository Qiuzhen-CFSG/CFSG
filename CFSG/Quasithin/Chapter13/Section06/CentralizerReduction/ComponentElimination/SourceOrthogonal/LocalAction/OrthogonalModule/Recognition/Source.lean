module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.SourceAction.Assembly
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Alternatives

/-!
# Source recognition of the orthogonal moved section

The genuine earlier configuration and all three conclusions of 13.6.23
give the ordinary FF assertion for K⁺ on U_K. Applying the complete
projective-line-corrected B.5.1 implication excludes every competing action:
the outer action excludes repeated natural modules, and the middle-node
minimal parabolic together with the moving seed excludes natural plus dual.
The selected A₈ coordinates extend to the whole plus group through its
compatible S₈ marking and the natural module's trivial linear centralizer.

Thus the literal [W_K,K]/C_[W_K,K](K), with its entire fixed kernel, is the
natural eight-point module. The explicit natural/orthogonal comparison
identifies it with orthogonal six-space equivariantly for the whole plus
action. The upper space is also the source U_K by 13.6.14.

Only the earlier source configuration (owned by
qt-13-06-rank-four-source-selection) and the universal corrected B.5.1
implication (owned by qt-b05-quasisimple) remain inputs. In particular,
neither component FF nor a classified module is an additional premise.
Extension from this moved section to the original seed span and the final
seed marking remain with qt-13-06-orthogonal-ff-seed-marking.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the paragraph
following 13.6.23, printed p.933/PDF p.950.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition
open ComponentSelection
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

universe u
variable {G : Type u} [Group G] [Finite G] {Ξ : GroupClass.{u}}
    {K L V : Subgroup G} {T : Sylow 2 G} {z v : G}
    (c : SourceAction.Configuration Ξ K L V T z v)
    (classification : ProjectiveLine.QuasisimpleClassificationInput.{u,u} Ξ)

include classification

/-- The full source hypotheses select the natural A₈ action on the actual
central quotient. The ordinary FF premise is constructed on this same upper
space, with the same elementary structure and component inclusion. -/
theorem source_component_natural :
    letI := c.elementary
    IsAlternatingNatural ((movedSection K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
      c.invariant c.lv_le).action.comp
        (plusImage K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed K).subtype) 8 := by
  let := c.elementary
  exact Alternatives.source_component_natural c classification
    (SourceAction.component_isFF c classification)

/-- Recognition of the requested literal moved section, with one compatible
S₈ actor and coordinates equivariant for its entire action. No source FF,
offender-generation, natural-module or dimension premise remains. -/
theorem source_naturalMovedSection :
    letI := c.elementary
    Nonempty (NaturalMovedSection K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed) := by
  let := c.elementary
  exact naturalMovedSection_of_component_natural K L (T : Subgroup G) z v
    c.lv_invariant c.seed_fixed c.invariant c.lv_le (T.isPGroup'.to_le inf_le_left)
    c.twoCore c.outside
    (movedSection K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed c.invariant c.lv_le)
    (source_component_natural c classification)

/-- The actual orthogonal-model consumer, including the source U_K identity.
The six-dimensional conclusion follows from full action coordinates on the
literal quotient; its central kernel has not been removed or split. -/
theorem source_orthogonalCoordinates :
    letI := c.elementary
    ∃ d : NaturalMovedSection K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed,
      (∀ w : Additive (WK K L (T : Subgroup G) z v), w ∈ d.upper.toSubmodule ↔
        (w.toMul : G) ∈ UX L z v (starImage z v K)) ∧
      Module.finrank (ZMod 2) (d.upper.toSubmodule ⧸ d.central.toSubmodule) = 6 ∧
      ∀ g w, d.orthogonalCoordinates K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
          (d.central.quotientRepresentation g w) =
        (Atlas.Order20160A8.DeletedEight.orthogonalHom (d.actor g)).val
          (d.orthogonalCoordinates K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed w) := by
  let := c.elementary
  obtain ⟨d⟩ := source_naturalMovedSection c classification
  refine ⟨d, ?_, d.section_finrank K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed,
    d.orthogonal_equivariant K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed⟩
  intro w
  exact (d.upper_mem w).trans
    ((movedSection_upper_mem K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
      c.invariant c.lv_le w).symm.trans
        (movedSection_upper_source K L (T : Subgroup G) z v c.lv_invariant c.seed_fixed
          c.selected c.invariant c.lv_le w))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition
