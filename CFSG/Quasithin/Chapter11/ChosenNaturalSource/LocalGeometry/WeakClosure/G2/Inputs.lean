module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.RootTransfer

/-!
# Concrete geometry still needed in the G₂ weak-closure proof

These are output specifications for two independent B.4.6 calculations.
The marking is the actual G₂ natural action on V/C_V(L). RootPlaneData
retains the three-space as an L-conjugate of the original flag preimage,
the root preimages inside V^g, and the two literal families of planes.
Neither weak-closure centralization nor any ambient normalizer bound is
part of the specification. The common-plane calculation is permitted to
use the containment in V^g, which RootTransfer proves from r>2n.

PlaneComponents is the preceding 11.1.3 conclusion on those same planes,
including its ambient conjugates. It is a separate earlier-source premise.
The assembly remains conditional until the model specifications below are
constructed. Source: B.4.6(3,9,12), pp.88--90, and 11.2.2, pp.767--768.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2
variable {G : Type*} [Group G] [Finite G]

/-- The exact 11.1.3 conclusion on the L-plane orbit and all its ambient
conjugates. Components are taken inside each plane normalizer. -/
def PlaneComponents (L P : Subgroup G) : Prop :=
  ∀ (g : G) (U I : Subgroup G), I ∈ planeFamily
      (L.map (MulAut.conj g).toMonoidHom) (P.map (MulAut.conj g).toMonoidHom) U →
    Source.UniqueNoncentralComponent (normalizer (I : Set G)) I
      (localResidual (L.map (MulAut.conj g).toMonoidHom) I)

variable {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

variable {F : BinaryField} {c : Coordinates D F}

/-- The model-specific conclusion of B.4.6(12), expressed on the original
actor image and the actual radical R₁. Its construction remains required. -/
def R1FamilyLocalization (f : InvariantFlag c) : Prop :=
  letI := D.elementary
  ∀ A : Subgroup G, A ≤ f.Ri 0 →
    ChapterE.inducedAutomizer V A ∈ ChapterE.fixedSpaceFamily
      (@ChapterE.automizerRepresentation G _ V D.elementary) (2 * S.field.degree - 1) →
    f.Vi 2 ≤ centralizer (A : Set G)

variable
    (marking : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (Coordinates.g2 marking))

/-- Output of the long-root and conjugate-plane calculation for a specified
noncentral conjugate. No weak-closure conclusion is included. -/
structure RootPlaneData (g : G) where
  threeSpace : Subgroup G
  marked_threeSpace : ∃ l : L,
    threeSpace = (f.Vi 2).map (MulAut.conj (l : G)).toMonoidHom
  rootSpan : RootSpan V (V.map (MulAut.conj g).toMonoidHom) threeSpace S.field.degree
  common_planes : threeSpace ≤ V.map (MulAut.conj g).toMonoidHom →
    planeFamily L (f.Vi 1) threeSpace = planeFamily
      (L.map (MulAut.conj g).toMonoidHom)
      ((f.Vi 1).map (MulAut.conj g).toMonoidHom) threeSpace
  original_generation : threeSpace ≤ V.map (MulAut.conj g).toMonoidHom →
    planeResidualSpan L (planeFamily L (f.Vi 1) threeSpace) = L
  conjugate_generation : threeSpace ≤ V.map (MulAut.conj g).toMonoidHom →
    planeResidualSpan (L.map (MulAut.conj g).toMonoidHom)
      (planeFamily (L.map (MulAut.conj g).toMonoidHom)
        ((f.Vi 1).map (MulAut.conj g).toMonoidHom) threeSpace) =
      L.map (MulAut.conj g).toMonoidHom

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2
