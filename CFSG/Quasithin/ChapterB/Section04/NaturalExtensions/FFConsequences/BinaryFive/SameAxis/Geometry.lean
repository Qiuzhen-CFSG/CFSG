module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.Contracts

/-!+# The literal rank-four configuration in the same-orientation case

The difficult case of B.4.9 uses a rank-four subgroup of the radical at a
three-space. Its intersection with the factor fixing a hyperplane has order
two. Both radicals below are pulled back through the coherent natural
marking, so all intersections and normalizers remain in the original group.

These definitions specify intermediate geometric obligations. In particular,
neither normalizer generation nor quadraticity on the extension is assumed
in `RankFourPosition`. Source: Aschbacher–Smith, combined manuscript of
1 March 2004, B.4.9, final paragraph on printed p.95.
-/

@[expose] public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive.SameAxis
open QuasisimpleSource BinaryLinear.OuterCyclic
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V}

/-- The actual block radical in the original acting group. -/
noncomputable def markedRadical (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)
    (W : Submodule (ZMod 2) (Space 5)) : Subgroup G :=
  (BinaryLinear.radical W).comap (groupEquiv d hF).toMonoidHom

/-- The source's rank-four position, with its order-two intersection.
For `R = markedRadical W`, the factor `R₁` is `R ⊓ markedRadical H`.
Since `B ≤ R`, the subgroup below is exactly `B ⊓ R₁`. -/
structure RankFourPosition (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)
    (B : Subgroup G) (W H : Submodule (ZMod 2) (Space 5)) : Prop where
  dim_three : Module.finrank (ZMod 2) W = 3
  dim_hyperplane : Module.finrank (ZMod 2) H = 4
  le_hyperplane : W ≤ H
  le_radical : B ≤ markedRadical d hF W
  rank_four : rank B = 4
  intersection_card : Nat.card (B ⊓ markedRadical d hF H : Subgroup G) = 2

/-- Either the offender already contains an axis four-group, or it occupies
the rank-four position in an ambient radical containing such a four-group.
This asserts geometry on the literal quotient, without upstairs quadraticity. -/
def PlacementAlternative (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)
    (B : Subgroup G) : Prop :=
  (∃ E : Subgroup G, E ≤ B ∧ QuadraticSplitting.IsAxisFour d E) ∨
    ∃ W H : Submodule (ZMod 2) (Space 5), RankFourPosition d hF B W H ∧
      ∃ E : Subgroup G, E ≤ markedRadical d hF W ∧ QuadraticSplitting.IsAxisFour d E

/-- The two concrete generation statements used in the propagation proof.
The first is generation by `B` under the simultaneous normalizer of `R`
and `C`; the second is generation by `C` under the normalizer of `R`.
These are conclusions to prove from `RankFourPosition`, not source premises. -/
def NormalizerGeneration (B C R : Subgroup G) : Prop :=
  (R ≤ ⨆ x : (Subgroup.normalizer R ⊓ Subgroup.normalizer C : Subgroup G),
    B.map (MulAut.conj (x : G)).toMonoidHom) ∧
  (R ≤ ⨆ n : (Subgroup.normalizer (R : Set G) : Subgroup G),
    C.map (MulAut.conj (n : G)).toMonoidHom)

end CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive.SameAxis
