module
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.FifthCycle
public import Theory.Representation.CommutingOddCentralCover

/-!
# Central covers of the deleted tensor square

The specified five-cycle is fixed-free on each factor of the actual deleted
square. The commuting odd norm therefore eliminates the central kernel of
any commutator-generated cover, yielding an actual representation equivalence.
This removes a cover-splitting premise in the deleted alternative of D.3.7.

Source: Aschbacher–Smith,D.3.7, printed pp.197–199.
-/

public section
open Representation
namespace BinaryPermutation.FiveTensorSquare
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  {τ : Representation (ZMod 2) (Alt × Alt) U}

/-- The original central cover map onto the deleted square is injective. -/
theorem centralCover_injective (p : τ.IntertwiningMap deletedAction)
    (hp : OneCohomology.IsCover p) : Function.Injective p :=
  OneCohomology.injective_of_cover_product_odd p hp fifthCycle 5 (by decide)
    fifthCycle_pow_five fifthCycle fifthCycle_left_fixed fifthCycle_right_fixed

/-- The cover itself, with its specified coordinate map, is the deleted tensor square. -/
noncomputable def centralCoverEquiv (p : τ.IntertwiningMap deletedAction)
    (hp : OneCohomology.IsCover p) : τ.Equiv deletedAction :=
  Representation.Equiv.mk (LinearEquiv.ofBijective p.toLinearMap
    ⟨centralCover_injective p hp,hp.1⟩) p.isIntertwining'

end BinaryPermutation.FiveTensorSquare
