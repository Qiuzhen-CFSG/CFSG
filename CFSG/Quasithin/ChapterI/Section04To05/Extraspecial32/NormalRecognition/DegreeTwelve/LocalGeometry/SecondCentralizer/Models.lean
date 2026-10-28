module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.ModelTypes

/-!
# Marked models for the second involution centralizer

The second involution is the central element of `C₂ × Sₙ`. The first ambient
class consists of the even involutions in the symmetric factor with trivial
central coordinate. The other ambient class contains all remaining involutions;
it is not the internal conjugacy class of the central element.

`LocalSeed` separates the local construction of `C_M(t)` and its Sylow placement
from the two transfers and recognition of the whole centralizer. `MarkedModel`
records the result needed to transport the mixed-pair fiber. Neither structure
is asserted here to follow from the original source hypotheses.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 4.1–4.3.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer

open Subgroup

variable {G : Type*} [Group G]

/-- The complete marking required for ambient mixed-pair transport. -/
public structure MarkedModel (z t : G) (n : ℕ) where
  equiv : Centralizer t ≃* Model n
  central : equiv (distinguished t) = centralInvolution n
  first : ∀ x : Centralizer t, IsConj z (x : G) ↔ FirstClass (equiv x)

/-- The local subgroup `C_M(t) ≃ C₂ × S₄`, with the full Sylow and
centralizer information used by the two transfers in source 4.2.
The centralizer condition is inside the literal `C_G(t)`. -/
public structure LocalSeed (z t : G) where
  embed : Model 4 →* Centralizer t
  injective : Function.Injective embed
  central : embed (centralInvolution 4) = distinguished t
  first : ∀ x : Model 4, IsConj z (embed x : G) ↔ FirstClass x
  sylow_card : ∀ S : Sylow 2 (Centralizer t), Nat.card S = 16
  centralizer_le : ∀ x : Model 4, FirstClass x →
    centralizer ({embed x} : Set (Centralizer t)) ≤ embed.range

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
