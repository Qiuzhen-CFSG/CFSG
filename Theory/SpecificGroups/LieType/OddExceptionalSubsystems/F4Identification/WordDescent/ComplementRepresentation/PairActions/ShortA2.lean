module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.Transport
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.Coordinates
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.ShortA2.DiagonalModel

/-!
# Assembly of the short A2 complementary action from two marked models

The diagonal action of the two E6 end chains is constructed in `Diagonal`.
The shared SL3 generators and their generation theorem are in `Model`.
`DiagonalModel` transports a marked representation of one E6 chain to the
complement, including its exact folded generator comparison.

This module applies the faithful-model transport to the actual F4 subgroup
on nodes 2 and 3. Two independent inputs remain explicit: a faithful marked
SL3 homomorphism to the F4 cover and a marked SL3 homomorphism to the first
E6 chain. Their existence is not asserted by the conditional constructor.
In particular no global F4 descent or identification is used, and there is
no irreducibility or characteristic-three exclusion.

The source is the common-lattice subsystem construction of GLS3 §2.6.2
(`refs/KGroup/GLS3/chapter2.tex`), used for the folded inclusion in
Aschbacher--Smith A.2.17, printed p.39 of `refs/quasithin.pdf`. Once the two
model comparisons are supplied, `pairActionsOfAdjacent` consumes
the resulting marked action and its rank-one restrictions.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
open WordDescent

variable (F : Type*) [Field F]

/-- Conditional assembly from the faithful F4 model and one marked E6 chain.
The diagonal action supplies the entire complementary comparison. -/
def shortA2PairActionOfModels
    (ι : ShortA2.Model F →* Cover F) (hι : Function.Injective ι)
    (hsource : ∀ (s k : Bool) (t : F),
      ι (ShortA2.modelGenerator F s k t) = coverSimple F s (pairNode 2 3 k) t)
    (η : ShortA2.Model F →* splitCarrier F)
    (htarget : ∀ (s k : Bool) (t : F),
      η (ShortA2.modelGenerator F s k t) = simpleRoot F s (ShortA2.leftNode k) t) :
    PairAction F 2 3 :=
  pairActionOfFaithfulModel F 2 3 ι hι (ShortA2.modelGenerator F) hsource
    (ShortA2.modelComplementAction F η htarget)
    (ShortA2.modelComplementAction_generator F η htarget)

@[simp] theorem shortA2PairActionOfModels_generator
    (ι : ShortA2.Model F →* Cover F) (hι : Function.Injective ι)
    (hsource : ∀ (s k : Bool) (t : F),
      ι (ShortA2.modelGenerator F s k t) = coverSimple F s (pairNode 2 3 k) t)
    (η : ShortA2.Model F →* splitCarrier F)
    (htarget : ∀ (s k : Bool) (t : F),
      η (ShortA2.modelGenerator F s k t) = simpleRoot F s (ShortA2.leftNode k) t)
    (s k : Bool) (t : F) :
    (shortA2PairActionOfModels F ι hι hsource η htarget).hom
        (pairGenerator F 2 3 s k t) =
      eigenspaceAction F (-1) (f4Simple F s (pairNode 2 3 k) t) :=
  (shortA2PairActionOfModels F ι hι hsource η htarget).map_generator s k t

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
