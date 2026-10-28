module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.Coordinates
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarData
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.Comparison
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Image.StarOrder

/-!
# Certificates for the concrete local conjugation image

The actual normal closure has bijective binary coordinates and acts trivially
on itself, by `localKernel_le_action_ker_certified`. The finite pair labels in
`Image.StarData` intertwine the proposed star permutations with the certified
right-conjugation masks and distinguish permutations of the stars.

The paired-generator comparison identifies the actual left-conjugation image
with the star group. A certified relabeling embeds that group into M24, and
stabilizer transversals supply the matching lower bound. Transporting the
resulting star-group order gives `actionImage_card`. Together with the exported
kernel containment, this supplies the image certificate for the quotient-count
reduction in `Action`.

Source: the ATLAS `J4G1-max1W1` words documented in `Cardinality.Subgroup`;
see the imported modules for the coordinate and star-witness constructions.
-/

namespace Janko4.Cardinality.QuotientCount

/-- The image of left conjugation on the actual local normal closure has M24 order. -/
public theorem actionImage_card
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    Nat.card (ActionImage hA hB) = 244823040 :=
  (Nat.card_congr (Image.actionImageEquivStarGroup hA hB).toEquiv).trans
    Image.starGroup_order

end Janko4.Cardinality.QuotientCount
