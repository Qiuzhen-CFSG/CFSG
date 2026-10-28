module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.Action

/-!
# Intermediate outputs for the local-cover assembly

`OrientedBorelData` is the output still required from the Borel argument,
not an alternative definition of the rank-two setup. It records an actual
interchange of both original planes and a root subgroup up to inner choice
of coordinates. It does not assert n=2, the center plane, or a centralizer
identity involving either plane.

`ResidualPlaneData` is the remaining natural-action output: the component
residual is the full opposite-plane residual, the two residuals generate Y,
and the second has an order-three element outside L. The assembly must
construct this data; it cannot treat these projections as source theorems.
The separate model calculations below are the precise intrinsic cover
inputs permitted by the conditional contract. They use the same projective
marking and require full automorphism coverage, not merely a family tag.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
proof of 15.3.38, printed pp.1135--1136.
-/

@[expose] public section
open Subgroup
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
variable {G : Type*} [Group G]

/-- Output of the source Borel and natural-plane argument. -/
structure OrientedBorelData (M Yplus S L V₁ V₂ : Subgroup G)
    {n : ℕ} (c : ProjectiveMarking L (2 ^ n)) where
  W₁ : Subgroup G
  W₂ : Subgroup G
  planes : PlaneOrder V₁ V₂ W₁ W₂
  first_le_sylow : W₁ ≤ S
  second_le_component_sylow : W₂ ≤ S ⊓ L
  second_card : Nat.card W₂ = 4
  second_invariant : S ≤ normalizer (W₂ : Set G)
  t : G
  t_mem : t ∈ M
  sylow_invariant : S.map (MulAut.conj t).toMonoidHom = S
  first_interchange : W₁.map (MulAut.conj t).toMonoidHom = W₂
  second_interchange : W₂.map (MulAut.conj t).toMonoidHom = W₁
  component_centralizes : componentPart Yplus L ≤ centralizer (W₁ : Set G)
  component_moves : ⁅W₂, componentPart Yplus L⁆ = W₂
  sylow_centralizer : S ⊓ centralizer (componentPart Yplus L : Set G) =
    S ⊓ centralizer (L : Set G)
  component_core : (componentPart Yplus L).pCoreIn 2 = S ⊓ L
  component_quotient : Nat.card
    (componentPart Yplus L ⧸ pCore 2 (componentPart Yplus L)) = 3
  root : RootInPlane c W₂

/-- Output of residual identification from the natural action and E₉ quotient. -/
structure ResidualPlaneData (M Y Yplus L W₁ W₂ : Subgroup G) : Prop where
  component_eq : componentPart Yplus L = planeResidual M Y W₁
  generated : Y = componentPart Yplus L ⊔ planeResidual M Y W₂
  outside_actor : ∃ z ∈ planeResidual M Y W₂, orderOf z = 3 ∧ z ∉ L

/-- Precise intrinsic calculations for the actual cover and its diagonal factor.
The equality n=2 and all center/centralizer conclusions are absent. -/
structure CoverCalculations (S L D W₂ : Subgroup G) {q : ℕ}
    (c : ProjectiveMarking L q) : Prop where
  normalizes_sylow : D ≤ normalizer (S ⊓ L : Subgroup G)
  commutator : ⁅S ⊓ L, D⁆ = S ⊓ L
  root_fixed : (S ⊓ L) ⊓ centralizer (D : Set G) ≤ W₂ ⊔ centerImage L
  sylow_fixed : S ⊓ centralizer (D : Set G) ≤
    W₂ ⊔ (S ⊓ centralizer (L : Set G))
  automorphisms : ∀ α : MulAut PSL(3,c.F), ∃ l ∈ L, ∃ d ∈ D, ∃ s ∈ S,
    c.Realizes (l * d * s) α

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
