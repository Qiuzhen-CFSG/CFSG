module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Branches
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Centralizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Thompson
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Natural
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.RankOne
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.BinaryThreeCover
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.NaturalDual
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.NaturalDualThompson
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Irreducible
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Moving
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.NaturalDualCover
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Cubic

/-!
# Source preparation for the constrained orbit

Full moved-span inclusion or a nonzero fixed layer controls the ambient
centralizer. Once the point and full Thompson subgroups agree, the normal
quasisimple-core component argument proves movement and hence the actual
FF action. Neither movement nor the fixed-layer centralizer argument needs
a model for the orbit.

Every binary-three and rank-one natural cover has complete preparation from
its original conjugation coordinates, including nonzero fixed kernels. In
the binary-three four-space, the maximum-elementary action images fix a
common plane, giving Thompson-fixed representatives outside the kernel.
The marked natural–dual row generates the whole moved subgroup and now
forces Thompson fixedness on the original full module, so its preparation
has no quietness premise. Its cover with the original fixed kernel is also
prepared, using the positive-layer branch when that kernel is nonzero.
Zero-kernel irreducible rows generate the moved subgroup. Whenever three
divides the original component quotient order, point Thompson equality is
now proved without a fixedness premise, and all irreducible covers give
preparation with their original fixed kernels. Recognition of the remaining
quiet rows and preparation in the three-free branch still require proof,
as does the retained four-natural binary-three row. Minimality
excludes the distinct two-copy moved row in the local Thompson-moving branch.
The entire local Thompson-moving branch, including every positive full
fixed layer, now has preparation without a model-recognition premise.
In particular,
the terminal LinearFiveData supplies enough geometry through its natural
marking alone, so its literal action facts are reconstructed here.
Source: Aschbacher--Smith, 10.2.9, printed pp.751--752.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The half-Sylow case needs only the original Thompson normalization of L. -/
theorem thompson_eq_of_halfSylow (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hs : pointSylow T v = (T : Subgroup G) ⊓ normalizer (L : Set G)) :
    elementaryAbelianMaxJ (pointSylow T v) = elementaryAbelianMaxJ (T : Subgroup G) := by
  apply elementaryAbelianMaxJ_eq_of_intermediate (T : Subgroup G) (pointSylow T v) ?_ inf_le_left
  rw [hs]
  exact le_inf (sSup_le fun _ hA => hA.1) D.thompson_normalizes_component

/-- The source alternatives now discharge every preparation field. Only the
row-specific span and Thompson geometry remain as explicit inputs. -/
theorem Context.prepared_of_orbit_alternative (c : Context D t v I)
    (ha : ⁅D.fullModule,L⁆ ≤ orbitModule D v I ∨
      ⁅D.fullModule,L⁆ ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (he : elementaryAbelianMaxJ (pointSylow T v) = elementaryAbelianMaxJ (T : Subgroup G)) :
    Prepared D v I :=
  c.prepared_of_centralizer_of_thompson_eq (c.centralizer_le_of_orbit_alternative ha) he

/-- The actual consumer keeps the original quotient and reduced module. -/
theorem Context.actionFacts_of_orbit_alternative (c : Context D t v I)
    (ha : ⁅D.fullModule,L⁆ ≤ orbitModule D v I ∨
      ⁅D.fullModule,L⁆ ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (he : elementaryAbelianMaxJ (pointSylow T v) = elementaryAbelianMaxJ (T : Subgroup G)) :
    ActionFacts c := c.actionFacts (c.prepared_of_orbit_alternative ha he)

/-- The terminal source configuration supplies all preparation and FF-action
facts; the parabolic endgame needs no independent preparation assumption. -/
theorem Context.actionFacts_of_linearFiveData (c : Context D t v I) (m : LinearFiveData c) :
    ActionFacts c :=
  c.actionFacts_of_natural_three m.quotient m.natural

/-- General preparation is reduced to local Thompson fixedness with no full
L₀-fixed vectors. Full-module Thompson fixedness is not assumed or inferred
from local fixedness. This task's final owner retains the displayed source
obligation. -/
theorem preparationAt_of_quiet_fixed_free
    (hquiet : ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G) (_c : Context D t v I),
      elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G) →
      D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ → Prepared D v I) :
    PreparationAt T := by
  intro L D t v I c
  by_cases hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)
  · by_cases hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥
    · exact hquiet L D t v I c hJ hz
    · exact c.prepared_of_full_fixed_ne_bot hz
  · exact c.prepared_of_local_thompson_moves hJ

/-- In the remaining quiet branch, cubic component order needs only the
original full-span inclusion. The three-free branch stays separate; no
cubic-order premise is imposed on the source theorem. Both obligations
are retained by qt-d-10-nona5-point-constrained. -/
theorem preparationAt_of_quiet_orbits_and_three_free
    (horbit : ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G) (_c : Context D t v I),
      elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G) →
      D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ →
      3 ∣ Nat.card (L ⧸ pCore 2 L) → ⁅D.fullModule,L⁆ ≤ orbitModule D v I)
    (hfree : ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
      (t v : G) (I : Subgroup G) (_c : Context D t v I),
      elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G) →
      D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ →
      ¬ 3 ∣ Nat.card (L ⧸ pCore 2 L) → Prepared D v I) :
    PreparationAt T := by
  apply preparationAt_of_quiet_fixed_free
  intro L D t v I c hJ hz
  by_cases hd : 3 ∣ Nat.card (L ⧸ pCore 2 L)
  · exact c.prepared_of_orbit_alternative_of_three hd
      (Or.inl (horbit L D t v I c hJ hz hd))
  · exact hfree L D t v I c hJ hz hd

end CFSG.Quasithin.Chapter10.PointControl.Constrained
