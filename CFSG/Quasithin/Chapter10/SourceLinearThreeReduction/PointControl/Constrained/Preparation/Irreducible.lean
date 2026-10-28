module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Centralizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Quiet
public import Theory.Representation.BinaryConjugationSection.FixedSplitting

/-!
# Literal orbit preparation for irreducible rows

A point two-group fixes a nonidentity moved vector. Its component orbit is
nonzero and invariant, so an irreducible marking with zero kernel makes this
orbit the whole original moved subgroup. The quiet Thompson hypothesis then
supplies preparation and the literal FF action. This is the common orbit
argument for the orthogonal-minus and Suzuki rows of 10.1.1 in
Aschbacher–Smith 10.2.9, printed p.751.

Concrete row recognition and full-module fixedness remain with the final
assembly owner qt-d-10-nona5-point-constrained. The conclusions here concern
the original subgroup, its specified coordinates, and its literal action.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Stellmacher
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) L V} [IsIrreducible ρ]

/-- A zero-kernel irreducible moved factor lies in the literal point orbit. -/
theorem Context.moved_le_of_irreducible (c : Context D t v I)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥ ρ) :
    ⁅D.fullModule,L⁆ ≤ orbitModule D v I := by
  let P := pointSylow T v
  let W := ⁅D.fullModule,L⁆
  let A := conjugateSpanBy (W ⊓ centralizer (P : Set G)) L
  have hPW : P ≤ normalizer (W : Set G) :=
    (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T))
      c.escaping.sylow_normalizes).trans (source_moved_normalizer_local_containment D)
  have hfix := inf_centralizer_ne_bot_of_pGroups P W (T.isPGroup'.to_le inf_le_left)
    (source_original_full_moved_elementary D).isPGroup hPW (source_full_moved_ne_bot D)
  have hA : A = W := by
    rcases s.eq_kernel_or_section A bot_le (conjugateSpanBy_le inf_le_left s.normalized)
      (le_normalizer_conjugateSpanBy _ _) with hb | ht
    · exact False.elim (hfix (bot_unique ((le_conjugateSpanBy _ _).trans_eq hb)))
    · exact ht
  change W ≤ orbitModule D v I
  rw [←hA]
  exact conjugateSpanBy_mono le_rfl c.escaping.strict.le

/-- A marked quiet irreducible row gives complete preparation. -/
theorem Context.prepared_of_quiet_irreducible (c : Context D t v I)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥ ρ)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G)) :
    Prepared D v I := c.prepared_of_centralizer_of_thompson_eq
      (c.centralizer_le_of_moved_le (c.moved_le_of_irreducible s))
      (c.thompson_eq_of_fullModule_centralized hJ)

/-- Actual consumer: the irreducible row prepares the original reduced action. -/
theorem Context.actionFacts_of_quiet_irreducible (c : Context D t v I)
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥ ρ)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G)) :
    ActionFacts c := c.actionFacts (c.prepared_of_quiet_irreducible s hJ)
end CFSG.Quasithin.Chapter10.PointControl.Constrained
