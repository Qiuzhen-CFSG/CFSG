module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.RegularFunctions
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Spaces
public import Theory.Representation.PGroupRegularOrbit

/-!
# Reduction of extremal D₄ interpolation to dimension and finite cell sums

Left translations preserve right Borel covariance. On a finite unipotent cell,
a function with nonzero total sum generates the regular representation of the
two-group, so evaluation of covariant functions is surjective. An algebraic
dimension bound by the cell cardinality then makes evaluation injective.

This proves the assembly for both Borel signs, with the dimension bounds,
finite cardinalities and nonzero scalar sums still explicit. It does not yet
prove unconditional extremal interpolation. Those inputs require the D₄
polynomial-space and twisted root-coordinate calculations, including q = 2.

Source: GLS3, Definition 2.8.1 and Theorem 2.8.2; Steinberg,
`refs/KGroup/GLS3/Chapter2St2.tex`, Sections 12, 13.2(d) and 13.3(a).
The finite two-group step uses `Representation.PGroupRegularOrbit`.
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
open Theory.AlgebraicGroup
open Representation.PGroupRegularOrbit
open scoped BigOperators
universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- A nonzero finite cell sum makes evaluation surjective: the translates of
that function generate the regular representation of the finite two-group. -/
theorem cellEvaluation_surjective_of_sum (S : Geometry K) (n : ℕ) (hn : 0 < n)
    (P Q : Set S.roots.Root) (chi : TorusWeight S.torus)
    (hQ : IsPGroup 2 (RootSubgroupGenerated S.roots Q))
    (hsum : HasNonzeroCellSum S n P Q chi) :
    Function.Surjective (cellEvaluation S n P Q chi) := by
  classical
  let := finiteCell_finite S n hn Q
  let := Fintype.ofFinite (finiteCell S n Q)
  let E := cellEvaluation S n P Q chi
  obtain ⟨f, hf⟩ := hsum
  have hc : ringChar k ≠ 0 := by rw [ringChar.eq k 2]; decide
  have hp : IsPGroup (ringChar k) (finiteCell S n Q) := by
    rw [ringChar.eq k 2]
    exact finiteCell_isPGroup S n Q hQ
  have hnorm : (∑ g : finiteCell S n Q, regular g (E f)) ≠ 0 := by
    intro hz
    have he : (∑ g : finiteCell S n Q, regular g (E f)) 1 =
        ∑ g : finiteCell S n Q, f.val (cellInclusion S n Q g) := by
      simp only [Finset.sum_apply]
      change (∑ g : finiteCell S n Q, E f (g⁻¹ * 1)) = _
      exact Fintype.sum_equiv (Equiv.inv (finiteCell S n Q)) _ _
        (fun g => by simp only [mul_one]; rfl)
    apply hf
    rw [finsum_eq_sum_of_fintype, ← he]
    exact congrFun hz 1
  have hsurj := LinearMap.surjective_of_injective
    (orbitMap_injective hc hp regular (E f) hnorm)
  have ht (g : finiteCell S n Q) :
      E (leftTranslate S P chi (cellInclusion S n Q g⁻¹) f) = regular g (E f) := by
    ext x
    change (leftTranslate S P chi (cellInclusion S n Q g⁻¹) f).val
      (cellInclusion S n Q x) = f.val (cellInclusion S n Q (g⁻¹ * x))
    rw [leftTranslate_apply, map_mul]
  intro v
  obtain ⟨c, hc⟩ := hsurj v
  refine ⟨∑ g : finiteCell S n Q, c g •
    leftTranslate S P chi (cellInclusion S n Q g⁻¹) f, ?_⟩
  change E _ = v
  rw [← hc, map_sum]
  simp only [map_smul, ht]
  rfl

/-- Surjectivity and the dimension bound give actual evaluation injectivity. -/
theorem cellInjective_of_dimension_of_sum (S : Geometry K) (n : ℕ) (hn : 0 < n)
    (P Q : Set S.roots.Root) (chi : TorusWeight S.torus)
    (hQ : IsPGroup 2 (RootSubgroupGenerated S.roots Q))
    [FiniteDimensional k (covariantSpace S P chi)]
    (hdim : Module.finrank k (covariantSpace S P chi) ≤ Nat.card (finiteCell S n Q))
    (hsum : HasNonzeroCellSum S n P Q chi) : CellInjective S n P Q chi := by
  classical
  let := finiteCell_finite S n hn Q
  let := Fintype.ofFinite (finiteCell S n Q)
  have hs := cellEvaluation_surjective_of_sum S n hn P Q chi hQ hsum
  have heqdim : Module.finrank k (covariantSpace S P chi) =
      Module.finrank k (finiteCell S n Q → k) := by
    apply le_antisymm
    · simpa only [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card] using hdim
    · exact LinearMap.finrank_le_finrank_of_surjective hs
  have hi := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heqdim).mpr hs
  intro f hf hz
  have he : cellEvaluation S n P Q chi ⟨f, hf⟩ = cellEvaluation S n P Q chi 0 := by
    ext g
    exact hz g.val g.property
  exact congrArg Subtype.val (hi he)

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
open Theory.AlgebraicGroup
open ExtremalGrid
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Conditional assembly of both extremal evaluation statements. The algebraic
space bound and the finite root-coordinate norm calculation remain explicit. -/
theorem extremalCellInjectivity_of_dimension_of_sums (S : Geometry K) (n : ℕ)
    (hn : 0 < n) (hdim : DimensionBounds S n) (hcard : CellCardinalities S n)
    (hsum : CellSums S n) : ExtremalCellInjectivity S n := by
  constructor
  · let := hdim.1.1
    apply cellInjective_of_dimension_of_sum S n hn _ _ _
      (negativeRoots_isPGroup S) _ hsum.1
    rw [hcard.1]
    exact hdim.1.2
  · let := hdim.2.1
    apply cellInjective_of_dimension_of_sum S n hn _ _ _
      (positiveRoots_isPGroup S) _ hsum.2
    rw [hcard.2]
    exact hdim.2.2

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
