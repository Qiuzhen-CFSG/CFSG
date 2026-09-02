module

public import Stellmacher.SectionOne.Defs
open Theory.GroupAction
open Theory.ElementaryAbelian


namespace Stellmacher.SectionOne

universe u v

/-- The subgroup `F = [W,x]` associated with an involution `x` in Lemma 1.3.

Here `W` is the corrected odd core `O_{2'}(G)`. -/
@[expose] public def involutionCommutator
    (G : Type u) [Group G] (x : G) : Subgroup G :=
  ⁅oddCore G, Subgroup.zpowers x⁆

/-- The three alternatives in Stellmacher's Lemma 1.3.

The notation `[V,F] = n` in the source means that the action-commutator
subgroup has order `n`.  The fixed-point equalities in the last two
constructors express `|V/C_V(x)| = 4`.

Source: `refs/latex/stellmacher-n-group.tex`, lines 302--312. -/
public inductive LemmaOneThreeConclusion
    (G : Type u) (V : Type v) [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V] (x : G) (F : Subgroup G) : Prop
  | cyclicThree
      (_ : Nat.card (commutatorAction F V) = 4)
      (_ : Nonempty (F ≃* Multiplicative (ZMod 3)))
  | small
      (_ : Nat.card (commutatorAction F V) = 2 ^ 4)
      (_ : Nat.card V =
        4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V))
      (_ : Nonempty (F ≃* Multiplicative (ZMod 3)) ∨
        Nonempty (F ≃* Multiplicative (ZMod 5)) ∨
        Nonempty
          (F ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))))
  | extraspecial
      (_ : Nat.card (commutatorAction F V) = 2 ^ 6)
      (_ : Nat.card V =
        4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V))
      (_ : ⁅(Subgroup.center F).map F.subtype, Subgroup.zpowers x⁆ = ⊥)
      (_ : IsExtraspecial 3 F)
      (_ : Nat.card F = 3 ^ 3)

/-- **Stellmacher (1.3).** Let `x` be an involution and put `F=[W,x]`. If
`F` is a `p`-group and `|V/C_V(x)| ≤ 4`, then one of the three alternatives
in `LemmaOneThreeConclusion` holds.

Source: `refs/latex/stellmacher-n-group.tex`, lines 302--312. -/
public theorem lemma_one_three
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (h : Hypotheses G V) (x : G)
    (hx : Theory.Comparator.IsInvolution x)
    (p : ℕ) [Fact p.Prime]
    (hF : IsPGroup p (involutionCommutator G x))
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V)) :
    LemmaOneThreeConclusion G V x (involutionCommutator G x) := by
  sorry

end Stellmacher.SectionOne
