module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Moving
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.NaturalDualThompson

/-!
# Natural--dual preparation with the original fixed kernel

The crossed pair puts the fixed kernel of the moved subgroup inside the
full L₀-fixed layer. If this kernel is nonzero, the proved positive-layer
preparation applies. If it vanishes, the actual natural--dual normalizer
has no FF offender and fixes the original full module under J(T).
Thus preparation and its literal FF-action consumer require neither a
zero-kernel hypothesis nor a quietness hypothesis on the original marking.

Source: Aschbacher--Smith 10.1.1(5), 10.1.2 and 10.2.9,
printed pp.741--742 and 751. Recognition of the original marking and the
remaining source assembly belong to qt-d-10-nona5-point-constrained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- A positive original moved kernel supplies preparation, with no marking
or Thompson-fixedness premise. -/
theorem Context.prepared_of_moved_fixed_ne_bot (c : Context D t v I)
    (hfixed : sourceMovedFixed D ≠ ⊥) : Prepared D v I := by
  apply c.prepared_of_full_fixed_ne_bot
  intro hz
  apply hfixed
  rw [c.moved_fixed_eq_orbit_fixed]
  apply bot_unique
  apply (inf_le_inf_right _ ?_).trans_eq hz
  exact le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)

/-- The literal natural--dual cover prepares VI with its original fixed
kernel retained; the two kernel cases are both discharged. -/
theorem Context.prepared_of_naturalDual_cover (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    Prepared D v I := by
  by_cases hz : sourceMovedFixed D = ⊥
  · rw [hz] at s
    exact c.prepared_of_naturalDual e s
  · exact c.prepared_of_moved_fixed_ne_bot hz

/-- The natural--dual cover gives the faithful FF action on the actual
centralizer quotient, without discarding fixed vectors. -/
theorem Context.actionFacts_of_naturalDual_cover (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    ActionFacts c := c.actionFacts (c.prepared_of_naturalDual_cover e s)

end CFSG.Quasithin.Chapter10.PointControl.Constrained
