module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection.Contracts

/-!
# Transport through one envelope factor

The companion element centralizes the literal factor L. In the application
it is the product of all the other E.6.7 factors. Transporting U into V
by the combined element must put the L-coordinate in M when U moves L.
This separates the alternating and natural-module calculations from the
central-product assembly. It is an obligation, not a source theorem.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
E.6.7 and E.6.23, printed pp.246 and 254–255; C.1.7–13, pp.123–125.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection
variable {G : Type*} [Group G]

/-- The transporter calculation with a companion centralizing the factor.
No containing block or centralizer-product conclusion is assumed. -/
def FactorTransporter (L M U V : Subgroup G) : Prop :=
  ∀ l ∈ L, ∀ c ∈ centralizer (L : Set G),
    U.map (MulAut.conj (l * c)).toMonoidHom ≤ V → l ∈ M

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection
