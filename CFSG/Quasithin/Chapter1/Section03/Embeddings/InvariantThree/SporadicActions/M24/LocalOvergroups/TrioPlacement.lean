module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M24.LocalOvergroups.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M24.LocalOvergroups.TrioPlacement.Reduction
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.EightPointLine
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.TransitiveCoverage
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.TrioObstruction

/-!
# Reducibility or trio placement for an M₂₄ pair

Every source pair is reducible or lies in an actual translated standard trio
stabilizer. In the intransitive case, the checked Sylow-overgroup calculation
gives an octad; restriction to its actual A₈ action and the proved eight-point
line calculation give reducibility. In the transitive case, exhaustive native
Sylow double-coset coverage gives the required trio and its M₂₄ conjugator.
This covers both product orders 9,216 and 27,648, including possible sextet
cases. The octad branch excludes the order-27 complement by divisibility;
the transitive branch retains both orders.

`reducibleOrTrioPlacement` discharges both inputs of the conditional assembly.
The separately named guarded placement theorem takes exactly the additional
premise `¬ PairReducible`, supplied in the source by an irreducible extending
action. The original unqualified `TrioPlacement` remains unresolved.

The concrete elementary-nine subgroup in `TrioObstruction` preserves no
trio. Thus the proposed `TrioPlacement` contract would force this subgroup
to occur in no source pair. The theorem below makes that remaining conflict
explicit; it is not a proof of `TrioPlacement` or of Proposition 1.3.4.

The saved GAP diagnostic exhibits a Sylow subgroup permuting with this E₉
and a product of order 9,216. That pairing has not been certified in Lean.
The unconditional Lean result is the elementary-nine construction and its
noncontainment in every actual octad-trio stabilizer.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`). The source invokes both permutability
and an irreducibility sieve; the isolated `PairInput` has no irreducibility
hypothesis. The source theorem is not refuted by this placement obstruction.
-/

@[expose] public section

open Sporadic.Mathieu
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.M24PairAction

/-- The corrected target preserves the full pair-action exclusion as an
alternative to containment in an actual translated standard trio stabilizer. -/
def ReducibleOrTrioPlacement : Prop :=
  ∀ (S : Sylow 2 M24) (R : Subgroup M24), PairInput S R →
    PairReducible S.toSubgroup R ∨
      ∃ g : M24, R ⊔ S.toSubgroup ≤ conjugateTrioStabilizer g

/-- Conditional assembly from the two independent mathematical
inputs. Both product orders are retained in the transitive branch; the
octad branch excludes order 27 and lifts the eight-point invariant line. -/
theorem reducibleOrTrioPlacement_of_transitive_of_eightPointLine
    (htrans : TransitiveSmallSylowPlacement) (hline : EightPointPairLine) :
    ReducibleOrTrioPlacement := by
  intro S R h
  obtain ⟨hsolv, _, _, hcard⟩ := pair_product_data h
  rcases small_sylow_overgroup_geometry htrans S (R ⊔ S.toSubgroup)
      le_sup_right hsolv hcard with ⟨O, hO⟩ | htrio
  · exact Or.inl (pairReducible_of_eightPointPairLine hline S R h O hO)
  · exact Or.inr htrio

/-- Every source pair is reducible or is contained in a conjugate of the
actual standard trio stabilizer. Both intrinsic inputs are proved. -/
theorem reducibleOrTrioPlacement : ReducibleOrTrioPlacement :=
  reducibleOrTrioPlacement_of_transitive_of_eightPointLine
    transitiveSmallSylowPlacement eightPointPairLine

/-- An irreducible extending action rules out the first alternative.
The actual source supplies `¬ PairReducible` through `not_pairReducible`;
`reducibleOrTrioPlacement` supplies the other premise. -/
theorem trio_placement_of_not_pairReducible (hp : ReducibleOrTrioPlacement)
    {S : Sylow 2 M24} {R : Subgroup M24} (h : PairInput S R)
    (hirr : ¬ PairReducible S.toSubgroup R) :
    ∃ g : M24, R ⊔ S.toSubgroup ≤ conjugateTrioStabilizer g :=
  (hp S R h).resolve_left hirr

/-- The precise guarded placement used by an irreducible extending action,
with no additional geometric or finite-coverage premise. -/
theorem trio_placement_of_pairInput_of_not_pairReducible
    {S : Sylow 2 M24} {R : Subgroup M24} (h : PairInput S R)
    (hirr : ¬ PairReducible S.toSubgroup R) :
    ∃ g : M24, R ⊔ S.toSubgroup ≤ conjugateTrioStabilizer g :=
  trio_placement_of_not_pairReducible reducibleOrTrioPlacement h hirr

/-- Any source pair using the explicit E₉ would refute universal trio placement.
The pair-existence premise remains explicit and is not asserted here. -/
theorem not_trioPlacement_of_elementaryNine_pair
    (hpair : ∃ S : Sylow 2 M24, PairInput S TrioObstruction.elementaryNine) :
    ¬ TrioPlacement := by
  intro hp
  obtain ⟨S, hS⟩ := hpair
  obtain ⟨g, hg⟩ := hp S TrioObstruction.elementaryNine hS
  exact TrioObstruction.elementaryNine_not_le_conjugateTrioStabilizer g
    (le_sup_left.trans hg)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.M24PairAction

end
