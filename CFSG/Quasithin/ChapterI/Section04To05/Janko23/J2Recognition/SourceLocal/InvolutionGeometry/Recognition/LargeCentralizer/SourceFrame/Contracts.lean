module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.ReturningPair

/-!
# Independent source inputs to the marked frame

`CubicGeometry` is the part of 46.3 and 46.14 constructed in the normalizer
of the original two-core product. It has no selected involution, Sylow
assertion in an unknown centralizer, or recognition of that centralizer.
`OutsideCentralizerSizes` is the separate calculation inside H, obtained
from the minus-extraspecial core action of an outside involution.

The assembly in `SourceFrame` must produce both inputs before it can assert
the existence of `LocalFrame`. These are mathematical contracts, not source
existence theorems.

Source: Aschbacher, *Sporadic Groups* (1994), 46.3, 46.11, 46.14 and the
beginning of 47.1, printed pp.251,255,257–260.
-/

@[expose] public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame

variable {G : Type*} [Group G] [Finite G]

structure CubicGeometry {D : Seed G} (P : ReturningPair D) where
  U : Subgroup G
  X1 : Subgroup G
  X3 : Subgroup G
  R_card : Nat.card P.R = 64
  E_center : (center P.R).map P.R.subtype = P.E
  U_card : Nat.card U = 4
  disjoint : Disjoint P.E U
  elementary : IsElementaryAbelian 2 (P.E ⊔ U : Subgroup G)
  join_le_R : P.E ⊔ U ≤ P.R
  U_eq : P.R ⊓ centralizer (X1 : Set G) = U
  X1_card : Nat.card X1 = 3
  X1_normalizes : X1 ≤ normalizer (P.E : Set G)
  X1_transitive : ∀ e ∈ P.E, e ≠ 1 → ∀ f ∈ P.E, f ≠ 1 →
    ∃ x : X1, (x : G) * e * (x : G)⁻¹ = f
  X3_card : Nat.card X3 = 3
  X3_normalizes : X3 ≤ normalizer (U : Set G)
  X3_centralizes : X3 ≤ centralizer (P.E ⊔ X1 : Set G)
  X3_transitive : ∀ u ∈ U, u ≠ 1 → ∀ v ∈ U, v ≠ 1 →
    ∃ x : X3, (x : G) * u * (x : G)⁻¹ = v
  normalizer_intersection_card : ∀ t ∈ U, t ≠ 1 →
    Nat.card ↥(involutionCentralizer t ⊓ normalizer (P.R : Set G)) = 48

/-- The fixed subgroup in Q has order four; the full centralizer in H has
order sixteen. Neither statement concerns the unknown full C_G(t). -/
def OutsideCentralizerSizes (D : Seed G) : Prop :=
  ∀ t ∈ involutionCentralizer D.z, orderOf t = 2 → t ∉ ambientCore D.z →
    Nat.card ↥(involutionCentralizer t ⊓ ambientCore D.z) = 4 ∧
    Nat.card ↥(involutionCentralizer t ⊓ involutionCentralizer D.z) = 16

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame
