module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.Contracts

/-!
# The two remaining proper-support displacement calculations

For support {0,1}, bounds of nine for the upper root 01 and the product of roots
01 and 23 suffice: every nonidentity involution is conjugate to one of these
matrices, and every nontrivial elementary actor contains an involution. The common
fixed space of an actor is contained in that involution's fixed space.

This is an unproved producer contract. `proper_inner_estimate_of_involution_bounds`
retains it explicitly. Its producer must derive both inequalities on the original
module from faithful irreducibility and the displayed highest-vector relations;
neither a degree bound nor an assumed module catalogue supplies them.

Source application: Aschbacher–Smith K.3.2, printed pp.454–455; Guralnick–Malle,
Classification of 2F-modules II, author manuscript, Proposition 4.7, pp.25–26.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
open Representation Representation.BinaryOffender
open ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Two literal cyclic displacement bounds, to be proved from proper adjacent
highest-vector support. This is a producer contract, not a classification. -/
def ProperInvolutionBounds (σ : Representation (ZMod 2) Group V) : Prop :=
  ∀ v : V, v ≠ 0 → LocalHighestVector σ {0, 1} v →
    9 ≤ fixedCodim σ (Subgroup.zpowers (simpleUpper 0)) ∧
      9 ≤ fixedCodim σ (Subgroup.zpowers (simpleUpper 0 * simpleUpper 2))

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
