module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.Covers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M23.IntrinsicLine
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M23.TwoCoreCenter.Placement
public import Theory.Mathieu.M23.QuasithinGeometry.FourSetStabilizer.Basic
public import Theory.Mathieu.M23.QuasithinGeometry.FourSetStabilizer.Center
public import Theory.Mathieu.M23.QuasithinGeometry.FourSetStabilizer.TwoCore

/-!
# Transporting the four-set calculation to an M23 Sylow pair

The placement theorem identifies the actual product RS with the stabilizer of
the standard four-set through conjugations in the Witt-design M23. Two-cores
and their centers transport along this equivalence.

The double-transposition inverse image is defined independently in
`FourSetStabilizer.Basic`. The local two-core and center calculations identify
it with the stabilizer's two-core and give its center order four. Applying both
calculations proves the same center order for every actual pair product RS,
discharging the geometric premise of the intrinsic invariant-line argument.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`); GLS3, Table 5.3d. This route retains the
full concrete stabilizer and uses no splitting assertion for the semilinear
extension in the source table.
-/

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions
open Sporadic.Mathieu Sporadic.Mathieu.M23Geometry

/-- The two independent local calculations suffice for the actual pair product.
Both two-cores are computed inside the displayed subgroups of M23. -/
public theorem m23_pair_twoCore_center_card_of_fourSet_calculations
    {S : Sylow 2 M23} {R : Subgroup M23} (h : PairInput S R)
    (hcore : pCore 2 fourStabilizer = FourSetStabilizer.coreCandidate)
    (hcenter : Nat.card (center FourSetStabilizer.coreCandidate) = 4) :
    Nat.card (center (pCore 2 (R ⊔ (S : Subgroup M23) : Subgroup M23))) = 4 := by
  obtain ⟨e⟩ := m23_pair_fourStabilizer_equiv h
  let f : pCore 2 (R ⊔ (S : Subgroup M23) : Subgroup M23) ≃*
      FourSetStabilizer.coreCandidate :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr ((pCore_map_iso 2 e).trans hcore))
  exact (Nat.card_congr (centerCongr f).toEquiv).trans hcenter

/-- The center of the two-core of the actual M23 Sylow pair product has order
four. The two-core is computed inside RS, with no placement or model premise. -/
public theorem m23_pair_twoCore_center_card
    {S : Sylow 2 M23} {R : Subgroup M23} (h : PairInput S R) :
    Nat.card (center (pCore 2 (R ⊔ (S : Subgroup M23) : Subgroup M23))) = 4 :=
  m23_pair_twoCore_center_card_of_fourSet_calculations h
    FourSetStabilizer.fourStabilizer_twoCore_eq
    FourSetStabilizer.coreCandidate_center_card

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions
