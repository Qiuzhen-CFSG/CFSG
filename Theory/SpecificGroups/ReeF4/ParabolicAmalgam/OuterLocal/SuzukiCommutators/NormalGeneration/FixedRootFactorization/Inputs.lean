module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.RootWords
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates

/-!
# Geometric matching and the B₂ multiplication input

`RootWordLayout` matches a proved partition of actual positive F₄ roots with
our eight named relative root words. Its fields concern only root indices,
parity, and equality of roots. It assumes no matrix identities, fixedness,
subgroup generation, or subgroup orders. The geometric matching forces the positive support to cover all eight
indices and forces the Suzuki radical to avoid index zero; these finite
facts are proved below independently of the matrix calculations.

`MainParameterProduct` is the specialization at first parameter 1 of the
literal B₂ multiplication formula. The reduction expresses each central
parameter as a product of three main-curve words using this identity.
Constructing the layouts and proving this matrix formula remain obligations.

Source: GLS3 2.3.7 and Table 2.4, type V, in
`refs/KGroup/GLS3/chapter2.tex`; application to Aschbacher–Smith F.1.12(II)(i),
printed pp.263–264 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
namespace ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Theory.AlgebraicGroup
open RadicalCoordinates RadicalCoordinates.FixedCoordinates

/-- Match the geometric blocks with the literal words from `RootWords`.
The conditions on the two unused pair roots record that reflection fixes
orthogonal roots; they ensure `centralWord = rootWord` at odd indices. -/
structure RootWordLayout (k : Support) where
  blocks : RootBlocks k
  pairIndex : Fin (pairCount k) → Fin 8
  quartetIndex : Fin (quartetCount k) → Fin 8
  pair_odd (j) : (pairIndex j).val % 2 ≠ 0
  quartet_even (j) : (quartetIndex j).val % 2 = 0
  pair_long (j) : (blocks.roots (.inl (j, 0))).val = longRoot (pairIndex j)
  pair_short (j) : (blocks.roots (.inl (j, 1))).val = shortRoot (pairIndex j)
  pair_mixed (j) : mixedRoot (pairIndex j) = shortRoot (pairIndex j)
  pair_high (j) : highRoot (pairIndex j) = longRoot (pairIndex j)
  quartet_long (j) : (blocks.roots (.inr (j, 0))).val = longRoot (quartetIndex j)
  quartet_short (j) : (blocks.roots (.inr (j, 1))).val = shortRoot (quartetIndex j)
  quartet_mixed (j) : (blocks.roots (.inr (j, 2))).val = mixedRoot (quartetIndex j)
  quartet_high (j) : (blocks.roots (.inr (j, 3))).val = highRoot (quartetIndex j)

namespace RootWordLayout
open Theory.AlgebraicGroup.StandardRootSystem LargeLocalSeeds

/-- A commuting pair has an odd index, so cannot be the middle Levi block. -/
theorem pairIndex_ne_zero {k : Support} (L : RootWordLayout k) (j : Fin (pairCount k)) :
    L.pairIndex j ≠ 0 := by
  intro h
  have hh := L.pair_odd j
  simp [h] at hh

private theorem index_injective {k : Support} (L : RootWordLayout k) :
    Function.Injective (Sum.elim L.pairIndex L.quartetIndex) := by
  intro a b h
  let slot : Fin (pairCount k) ⊕ Fin (quartetCount k) → Slot k :=
    Sum.map (fun j => (j, 0)) (fun j => (j, 0))
  have hr (s : Fin (pairCount k) ⊕ Fin (quartetCount k)) :
      (L.blocks.roots (slot s)).val = longRoot (Sum.elim L.pairIndex L.quartetIndex s) := by
    cases s with
    | inl j => exact L.pair_long j
    | inr j => exact L.quartet_long j
  have he : L.blocks.roots (slot a) = L.blocks.roots (slot b) :=
    Subtype.ext (by rw [hr, hr, h])
  have hh := L.blocks.roots.injective he
  cases a <;> cases b
  · simpa [slot] using hh
  · simp [slot] at hh
  · simp [slot] at hh
  · simpa [slot] using hh

/-- Distinct geometric blocks give distinct main roots; the eight positive
blocks therefore cover the eight word indices. -/
theorem positive_covers (L : RootWordLayout .positive) (i : Fin 8) :
    (∃ j, L.pairIndex j = i) ∨ (∃ j, L.quartetIndex j = i) := by
  have hh := (Fintype.bijective_iff_injective_and_card
    (Sum.elim L.pairIndex L.quartetIndex)).mpr
      ⟨index_injective L,
        Fintype.card_congr (finSumFinEquiv : Fin 4 ⊕ Fin 4 ≃ Fin 8)⟩
  obtain ⟨j, hj⟩ := hh.2 i
  cases j with
  | inl j => exact Or.inl ⟨j, hj⟩
  | inr j => exact Or.inr ⟨j, hj⟩

/-- The Suzuki radical excludes the middle simple root, which is `longRoot 0`. -/
theorem radical_quartetIndex_ne_zero (L : RootWordLayout (.radical .suzuki))
    (j : Fin (quartetCount (.radical .suzuki))) : L.quartetIndex j ≠ 0 := by
  intro h
  have hr : IsRadicalRoot .suzuki (L.blocks.roots (.inr (j, 0))).val :=
    (L.blocks.roots (.inr (j, 0))).property
  rw [L.quartet_long, h] at hr
  obtain ⟨i, hi, hcoeff⟩ := hr.2
  fin_cases i
  · exact hcoeff (by norm_num [longRoot, typeF4SimpleCoefficient, typeF4SimpleRoot, basisVector])
  · exact hi (by simp [leviNodes])
  · exact hi (by simp [leviNodes])
  · exact hcoeff (by norm_num [longRoot, typeF4SimpleCoefficient, typeF4SimpleRoot, basisVector])

end RootWordLayout

/-- The B₂ product with first main parameter 1. No generation conclusion is
part of this predicate, and no normal-closure or perfectness premise occurs. -/
def MainParameterProduct (m : ℕ) : Prop :=
  ∀ i : Fin 8, i.val % 2 = 0 → ∀ u : CoefficientField m,
    rootWord m i 1 * rootWord m i u = rootWord m i (1 + u) * centralWord m i u

end ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
