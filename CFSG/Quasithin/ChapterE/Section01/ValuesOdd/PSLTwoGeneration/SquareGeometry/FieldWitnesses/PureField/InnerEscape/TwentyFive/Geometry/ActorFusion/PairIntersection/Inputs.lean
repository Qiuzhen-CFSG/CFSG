module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.ActorFusion.Inputs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.ActorFusion.PairIntersection.Intrinsic

/-!
# Independent root calculations for the projected overlap

The local calculation concerns the marked S₅ × C₂ centralizers and the
ambient linear coordinate. The independent rigidity calculation concerns
linear square roots of order four in the inner model. Neither assumes an intersection
bound, actor coverage, fusion, or generation. Their source-model proofs
remain required; `PairIntersection` assembles the two explicit inputs.

Source: Aschbacher--Smith E.1.14(6), printed p.214 (Asc82a, Lemma 4.10).
-/

public section
noncomputable section
open Subgroup GorensteinWalter Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame
variable {F : Type*} [Field F] [Finite F] {σ : F ≃+* F}
variable (c : Frame σ) (hF : Nat.card F = 5 ^ 2) (hσ : orderOf σ = 2)

namespace PairIntersection

/-- The twisted field involution lies in both marked large subgroups.
Every nonidentity linear element of either large subgroup has a linear
fourth root inside that literal centralizer. These are local model facts. -/
structure LocalSquareRoots : Prop where
  twist_mem : ∀ i, c.involution true ∈ c.large hF hσ i
  roots : ∀ i x, x ∈ c.large hF hσ i → (x : PGammaL2 F).right = 1 → x ≠ 1 →
    ∃ r : innerModel F σ, r ∈ c.centralizerAt i ∧
      (r : PGammaL2 F).right = 1 ∧ r ^ 2 = x ∧ orderOf r = 4

/-- Two linear square roots of order four with the same square differ by inversion;
a linear involution commuting with a linear element of order four is its
square. This is a statement about actual elements of the inner model. -/
structure LinearRootRigidity (F : Type*) [Field F] (σ : F ≃+* F) : Prop where
  same_square : ∀ r s : innerModel F σ,
    (r : PGammaL2 F).right = 1 → (s : PGammaL2 F).right = 1 →
    orderOf r = 4 → r ^ 2 = s ^ 2 → s = r ∨ s = r⁻¹
  central_involution : ∀ r z : innerModel F σ,
    (r : PGammaL2 F).right = 1 → (z : PGammaL2 F).right = 1 →
    orderOf r = 4 → orderOf z = 2 → Commute z r → z = r ^ 2

end PairIntersection

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame
