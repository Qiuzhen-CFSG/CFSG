module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.RankOne
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.BinaryThreeCover
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.DoubledExclusion

/-!+# Preparation in the original local Thompson-moving branch

Minimality and the given crossed pair exclude the doubled binary-three
moved quotient, retaining its original fixed kernel. The source B.5
classification therefore gives a rank-one or binary-three natural cover
whenever J(T) moves the local module. Both covers already prepare the
literal orbit VI, including positive fixed kernels. A positive full
L₀-fixed layer forces this local Thompson movement by source 3.1.8.

This supplies preparation and its actual FF-action consumer without a
model-recognition premise in either of these branches. The local quiet,
full fixed-free branch, including the four-natural row, and containing-model
recognition remain with
qt-d-10-nona5-point-constrained. No later generation bound is used.
The two-copy moved row excluded here differs from the four-copy moved
row in source 10.1.1(6), which remains a source obligation.
Source: Aschbacher--Smith B.5.6, 10.1.2 and 10.2.9,
printed pp.741--742 and 751; the doubled exclusion uses minimality and
the original cubic residual rather than source 10.2.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The doubled moved row is impossible on the actual minimal
crossed context, with its full fixed kernel still present. -/
theorem Context.not_binaryThreeDoubled (c : Context D t v I) :
    ¬ Selection.ModuleChoice.BinaryThreeDoubled D :=
  Selection.ModuleChoice.not_binaryThreeDoubled_of_minimal D c.minimal
    c.escaping.t_mem c.escaping.t_not_normalizes c.escaping.crossed

/-- Source recognition in the moving local branch gives one of the two
literal natural covers of the original moved subgroup. -/
theorem Context.natural_of_local_thompson_moves (c : Context D t v I)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)) :
    Selection.RankOneNatural D ∨ Selection.BinaryThreeNatural D := by
  rcases Selection.ModuleChoice.moving_local_natural_or_doubled D
      (fun hn => c.escaping.t_not_normalizes (hn c.escaping.t_mem)) c.nonA5 hJ
    with hr | hb | hd
  · exact Or.inl hr
  · exact Or.inr hb
  · exact (c.not_binaryThreeDoubled hd).elim

/-- The original local Thompson-moving branch needs no supplied model. -/
theorem Context.prepared_of_local_thompson_moves (c : Context D t v I)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)) : Prepared D v I := by
  rcases c.natural_of_local_thompson_moves hJ with hr | hb
  · exact c.prepared_of_rankOneNatural hr
  · exact c.prepared_of_binaryThreeNatural hb

/-- The moving branch supplies the faithful FF action on the literal VI. -/
theorem Context.actionFacts_of_local_thompson_moves (c : Context D t v I)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)) : ActionFacts c :=
  c.actionFacts (c.prepared_of_local_thompson_moves hJ)

/-- All positive full fixed layers are prepared from the original context. -/
theorem Context.prepared_of_full_fixed_ne_bot (c : Context D t v I)
    (hfixed : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥) :
    Prepared D v I :=
  c.prepared_of_local_thompson_moves
    (Selection.ModuleChoice.local_thompson_moves_of_full_fixed_ne_bot D c.many hfixed)

/-- Positive fixed vectors are retained in the actual reduced action. -/
theorem Context.actionFacts_of_full_fixed_ne_bot (c : Context D t v I)
    (hfixed : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥) :
    ActionFacts c := c.actionFacts (c.prepared_of_full_fixed_ne_bot hfixed)

end CFSG.Quasithin.Chapter10.PointControl.Constrained
