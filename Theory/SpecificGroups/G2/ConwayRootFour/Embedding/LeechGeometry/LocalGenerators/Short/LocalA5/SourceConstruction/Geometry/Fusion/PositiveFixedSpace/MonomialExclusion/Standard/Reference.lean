module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.Coordinates
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Sextet

/-!
# A reference quaternion pair for the standard Golay sextet

The reference pullbacks are translations by the full-support hexacode words
(b,b,b,b,b,b) and (c,a,c,a,c,a). Their signs are the binary lifts of the second
word and of the sum of the two words. `ReferenceQuaternionPair` specifies these
literal functions on the existing monomial group, rather than assigning a group
family label. The two remaining contracts separate pair normalization from the
fixed-space calculation in its actual quotient coordinates.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
and the root-four convention on p.269. The reference parameters use the existing
attributed ATLAS Golay encoder. Neither remaining contract is asserted here.
-/

open Atlas.Conway Atlas.Codes Atlas.Lattices
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion

/-- The hexacode word (b,b,b,b,b,b), in the existing encoder convention. -/
def referenceHexA : HexWord := hexEncoder (![1,1,1], ![0,0], 0)

/-- The hexacode word (c,a,c,a,c,a), in the existing encoder convention. -/
def referenceHexB : HexWord := hexEncoder (![0,0,0], ![1,0], 1)

def referencePullA (i : Omega) : Omega :=
  (i.1, rowLabel.symm (rowLabel i.2 + referenceHexA i.1))

def referencePullB (i : Omega) : Omega :=
  (i.1, rowLabel.symm (rowLabel i.2 + referenceHexB i.1))

/-- Both signs and both coordinate pullbacks of the marked pair. -/
def ReferenceQuaternionPair (a b : GolayMonomialGroup) : Prop :=
  a.left.toAdd.val = jWord referenceHexB ∧
  b.left.toAdd.val = jWord (referenceHexA + referenceHexB) ∧
  (∀ i, monomialPull a i = referencePullA i) ∧
  (∀ i, monomialPull b i = referencePullB i)

/-- The geometric/sign normalization still to be proved. Equal binary kernels
are essential input; no statement about the third element is needed. -/
def StandardQuaternionNormalization : Prop :=
  ∀ a b : GolayMonomialGroup,
    quaternionParts a b = distinguishedUnorderedSextet.val →
    (monomialEmbedding a) ^ 2 = negationIsometry →
    (monomialEmbedding b) ^ 2 = negationIsometry →
    (monomialEmbedding a * monomialEmbedding b) ^ 2 = negationIsometry →
    binaryFixed (monomialEmbedding a) = binaryFixed (monomialEmbedding b) →
    ∃ r : GolayMonomialGroup,
      ReferenceQuaternionPair (r * a * r⁻¹) (r * b * r⁻¹)

/-- The remaining finite calculation uses the proven literal quotient matrices.
It is a specialized bound for one signed pair, with no classification premise. -/
def ReferenceQuaternionBound : Prop :=
  ∀ a b m : GolayMonomialGroup,
    ReferenceQuaternionPair a b →
    (monomialEmbedding m) ^ 2 = 1 →
    Commute (monomialEmbedding m) (monomialEmbedding a) →
    Commute (monomialEmbedding m) (monomialEmbedding b) →
    8 ≤ Module.finrank Bit (StandardCoordinates.commonKernel a m)

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion
