module

public import Stellmacher.SectionOne.Defs
public import Stellmacher.SectionOne.InvolutionPGroupSmallIndexClassification
public import Stellmacher.SectionOne.OddCoreInvolution

/-!
# Stellmacher (1.3): small-index involutions

For a faithful elementary abelian 2-group action of a finite solvable group
with trivial 2-core, let an involution `x` have fixed-point index at most
four. If `F=[O₂′(G),x]` is a p-group, its action commutator and its group
structure lie in the three alternatives below.

The Fitting-centralizer argument makes `F` nontrivial; containment in the
odd core gives coprime order. Coprime commutator idempotence gives
`[F,x]=F`. The ambient-action adapter then restricts to `F⟨x⟩` acting on
`[V,F]`, applies the central-quotient induction and finite linear endpoints
of the reduced classification, and transports its alternatives back.
Source: refs/latex/stellmacher-n-group.tex, (1.3), journal pp. 15–16.
-/


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

-- This source-facing declaration retains its baseline placeholder while its proof is completed.
set_option warningAsError false in
/-- **Stellmacher (1.3).** Let `x` be an involution and put `F=[W,x]`. If
`F` is a `p`-group and `|V/C_V(x)| ≤ 4`, then one of the three alternatives
in `LemmaOneThreeConclusion` holds.

Source: `refs/latex/stellmacher-n-group.tex`, lines 302--312. -/
public theorem lemma_one_three
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (h : Hypotheses G V) (x : G)
    (hx : IsInvolution x)
    (p : ℕ) [Fact p.Prime]
    (hF : IsPGroup p (involutionCommutator G x))
    (hindex : Nat.card V ≤
      4 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers x) V)) :
    LemmaOneThreeConclusion G V x (involutionCommutator G x) := by
  have hFne : involutionCommutator G x ≠ ⊥ :=
    oddCore_involution_commutator_ne_bot h x hx
  have hFodd : Nat.Coprime 2 (Nat.card (involutionCommutator G x)) :=
    oddCore_involution_commutator_coprime x
  have hWnorm : (oddCore G).Normal := by
    change (pPrimeCore 2 G).Normal
    infer_instance
  let _ : (oddCore G).Normal := hWnorm
  have hRnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (oddCore G : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers x)) (Nat.card (oddCore G)) := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx.2 hx.1]
    exact pPrimeCore_coprime_card (G := G) (p := 2)
  have hcomm : ⁅involutionCommutator G x, Subgroup.zpowers x⁆ =
      involutionCommutator G x :=
    commutator_double_eq_self_of_coprime (Subgroup.zpowers x) (oddCore G) hRnorm hcop
  rcases involutionPGroup_smallIndex_classification_on_commutator
    (involutionCommutator G x) hFne p hF hFodd x hx hcomm hindex h.action_faithful
      with hsmall | hsmall | hlarge
  · exact .cyclicThree hsmall.1 hsmall.2
  · exact .small hsmall.1 hsmall.2.1 hsmall.2.2
  · exact .extraspecial hlarge.1 hlarge.2.1 hlarge.2.2.1 hlarge.2.2.2.1 hlarge.2.2.2.2

end Stellmacher.SectionOne
