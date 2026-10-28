module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Inputs
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner.NormalizedLift
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals

/-!
# The full paired transvection marking in 15.3.56

The coordinates here are adapted to E/Z and Eᵗ/Z. They are deliberately
separate from the K-natural/dual coordinates in `RecognizedAction`: the
source does not say that E/Z is a K-submodule. The actual quotient images
of E, Eᵗ and V₀ are marked. A surjection from the literal X onto the
concrete point radical, together with equivariance on every vector,
expresses the full center-transvection action on E/Z and its dual-axis
action on Eᵗ/Z simultaneously.

This is an earlier-source input interface. It does not assume an actor
commutator identity, containment in K, or an identification of the two
coordinate systems. Constructing that comparison is the remaining marked
actor calculation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.56(3–5) and 15.3.58(2), printed pp.1147–1149.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner
open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian

variable {G : Type*} [Group G]
variable (Z ZS : Subgroup G) [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- The literal image of A ∩ U in U/Z; all marking equalities use this map. -/
def vectorImage (A : Subgroup G) : Subgroup (VectorQuotient Z ZS) :=
  (A.subgroupOf (closureU Z ZS)).map (QuotientGroup.mk' _)

/-- The fixed center vector in coordinates adapted to E/Z. -/
def centerVector : BinaryLinearThree.Vector := ![1, 0, 0]

/-- Full, simultaneous center and dual-axis transvections on the actual pair.
`RecognizedAction.coordinates` is a different coordinate system and no
compatibility between the two splittings is silently assumed. -/
structure MarkedAction (V₀ : Subgroup G) (y t : G)
    (hXH : partnerX Z ZS y ≤ centralizerH Z) where
  coordinates : VectorQuotient Z ZS ≃* Multiplicative NaturalDualSpace
  E_image : ∀ w : VectorQuotient Z ZS,
    w ∈ vectorImage Z ZS (intersectionE Z ZS y) ↔ (coordinates w).toAdd.2 = 0
  Et_image : ∀ w : VectorQuotient Z ZS,
    w ∈ vectorImage Z ZS (rightConjugate (intersectionE Z ZS y) t) ↔
      (coordinates w).toAdd.1 = 0
  center_image : ∀ w : VectorQuotient Z ZS,
    w ∈ vectorImage Z ZS V₀ ↔
      ∃ a : ZMod 2, (coordinates w).toAdd = (a • centerVector, 0)
  parameter : partnerX Z ZS y →* Matrix.PSL3Two.MarkedAutomorphisms.pointV
  full : Function.Surjective parameter
  equivariant : ∀ (x : partnerX Z ZS y) (w : VectorQuotient Z ZS),
    (coordinates (quotientAction Z ZS ⟨x, hXH x.property⟩ w)).toAdd =
      (BinaryLinearThree.W (parameter x).val (coordinates w).toAdd.1,
        BinaryLinearThree.W.dual (parameter x).val (coordinates w).toAdd.2)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner
