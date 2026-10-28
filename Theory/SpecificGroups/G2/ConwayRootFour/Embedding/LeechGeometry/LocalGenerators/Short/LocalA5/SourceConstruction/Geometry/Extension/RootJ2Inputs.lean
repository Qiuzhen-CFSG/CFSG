module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.ConstructionInputs
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.LocalA5.Seeds

/-!
# Marks for transporting a root J₂ into the long-frame geometry

The permutation J₂ has a specified cubic X, dihedral B, and inverter in
C_J₂(B). To use its proved centralizer calculation, the actual map to the
Leech quotient must carry X over the long cubic, carry B over the placed
D₁₀, and give the inverter the graph action in the original coordinates.
`RootJ2Marks` records only these comparisons; it asserts no A₅ existence
or faithfulness. The consumer in `Geometry.Extension` proves that the image
of C_J₂(B) is the required A₅.

A comparison with the icosian carrier gives a genuine root J₂ map. Conjugating
by an element of C(I) preserves its containment in C(I). Neither the carrier
comparison nor a conjugator aligning these marks is constructed here.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284:
the choice of the root J₂ uses 49.1, and its placement uses 48.8 (p.273).
The fixed permutation marks come from the checked 47.2/47.10 development.
-/

open Atlas.Conway
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
open OctonionLocals

/-- The three literal marks needed to transport the source D₁₀ centralizer. -/
structure RootJ2Marks (L : LongFrame)
    (f : Sporadic.LeechRelated.J2.Carrier →* LeechCentralQuotient) where
  cubic_le : (longCubic L).range ≤
    Sporadic.LeechRelated.J2.RecognitionGeometry.X.map f
  dihedral_le : (dihedralLift L).range ≤
    Sporadic.LeechRelated.J2.RecognitionGeometry.B.map f
  reflection_on_single : ∀ j a,
    quotientModTwoRepresentation
        (f Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5.inverter)
        (L.coordinates (Pi.single j a)) =
      L.coordinates (action graph (Pi.single j a))

/-- A conjugate of the actual icosian J₂ embedding after carrier comparison. -/
def conjugatedRootJ2
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (g : LeechCentralQuotient) :
    Sporadic.LeechRelated.J2.Carrier →* LeechCentralQuotient :=
  (MulAut.conj g).toMonoidHom.comp (icosianProjectiveToCo1.comp e.toMonoidHom)

theorem conjugatedRootJ2_mem
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    {g : LeechCentralQuotient} (hg : g ∈ centralizerI)
    (a : Sporadic.LeechRelated.J2.Carrier) :
    conjugatedRootJ2 e g a ∈ centralizerI :=
  centralizerI.mul_mem (centralizerI.mul_mem hg (janko_mem_centralizerI (e a)))
    (centralizerI.inv_mem hg)


end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
