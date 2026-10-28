module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Passage
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.Unipotent
public import Theory.AlgebraicGroup.Tori.Power

/-!
# Fixed tori and opposite unipotents in characteristic two

The three subgroups here are literal intersections inside the full graph-field
fixed group. Both unipotent intersections lie in its elementary subgroup.
Squaring on the torus is injective in characteristic two; finiteness therefore
supplies square roots in the fixed torus and excludes even torus order.

Two complementary torus reductions are proved. The source argument conjugates
an elementary inversion representative by a fixed square root. For type D4,
one can instead use an opposition lift whose square is in the torus: that
square is trivial, and every torus translate of the lift is an involution.
Neither reduction asserts existence of the actual opposition representative.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 11.10 and 12.2--12.4.
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
open Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The literal intersection of the supplied torus with graph-field fixed points. -/
def fixedTorus (S : Geometry K) (n : ℕ) :
    Subgroup (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n) :=
  S.torus.toSubgroup.comap
    (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n).subtype

/-- Positive unipotent points in the full graph-field fixed group. -/
def fixedPositive (S : Geometry K) (n : ℕ) :
    Subgroup (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n) :=
  (RootSubgroupGenerated S.roots S.roots.positive).comap
    (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n).subtype

/-- Negative unipotent points in the full graph-field fixed group. -/
def fixedNegative (S : Geometry K) (n : ℕ) :
    Subgroup (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n) :=
  (RootSubgroupGenerated S.roots (S.roots.neg ⁻¹' S.roots.positive)).comap
    (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n).subtype

/-- A characteristic-two torus has no ambiguity in square roots on points. -/
theorem torus_sq_injective (S : Geometry K) {x y : Variety.Point K}
    (hx : x ∈ S.torus) (hy : y ∈ S.torus) (hxy : x ^ 2 = y ^ 2) : x = y := by
  obtain ⟨a, rfl⟩ := (Set.ext_iff.mp S.torus.range_inclusion x).mpr hx
  obtain ⟨b, rfl⟩ := (Set.ext_iff.mp S.torus.range_inclusion y).mpr hy
  have hinj : Function.Injective (fun t : Variety.Point S.torus.carrierVariety =>
      t ^ 2) := by
    simpa only [pow_one] using
      (IsTorus.pow_primePower_bijective S.maximalTorus.1 2 1).1
  exact congrArg S.torus.inclusion.onPoints
    (hinj (S.torus.inclusion_injective (by simpa only [map_pow] using hxy)))

/-- Squaring stays injective after intersecting with the literal fixed group. -/
theorem fixedTorus_sq_injective (S : Geometry K) (n : ℕ) :
    Function.Injective (fun t : fixedTorus S n => t ^ 2) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact torus_sq_injective S x.property y.property
    (congrArg (fun t : fixedTorus S n => ((t : graphFieldFixedSubgroup
      S.diagram.toMulEquiv S.frobenius.onPoints n) : Variety.Point K)) hxy)

/-- Every fixed torus point has a square root in the fixed torus itself,
including at exponent one. Finiteness turns injectivity into surjectivity. -/
theorem fixedTorus_square_surjective (S : Geometry K) (n : ℕ) (hn : 0 < n) :
    Function.Surjective (fun t : fixedTorus S n => t ^ 2) := by
  let := S.fixed_finite n hn
  exact Finite.surjective_of_injective (fixedTorus_sq_injective S n)

/-- The actual fixed torus has odd order; no torus order formula is needed. -/
theorem fixedTorus_card_odd (S : Geometry K) (n : ℕ) (hn : 0 < n) :
    Odd (Nat.card (fixedTorus S n)) := by
  let := S.fixed_finite n hn
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := fixedTorus S n) 2 h
  have ht2 : t ^ 2 = (1 : fixedTorus S n) ^ 2 := by
    rw [one_pow, ← ht]
    exact pow_orderOf_eq_one t
  have ht1 := fixedTorus_sq_injective S n ht2
  simp only [ht1, orderOf_one] at ht
  omega

/-- The opposite Borel radical is a two-group on algebraic points. -/
theorem negativeRoots_isPGroup (S : Geometry K) :
    IsPGroup 2 (RootSubgroupGenerated S.roots (S.roots.neg ⁻¹' S.roots.positive)) := by
  rw [← S.bigCell.data.opposite_witness.root_generated]
  exact S.bigCell.data.opposite_witness.unipotent.isPGroup_of_unipotent
    S.bigCell.data.opposite_witness.radical.2.1 2

/-- All negative unipotent fixed points belong to the elementary subgroup. -/
theorem fixedNegative_le_elementary (S : Geometry K) (n : ℕ) :
    fixedNegative S n ≤
      graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n := by
  intro x hx
  have hU := (negativeRoots_isPGroup S).comap_of_injective
    (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n).subtype
    Subtype.coe_injective
  obtain ⟨m, hm⟩ := hU ⟨x, hx⟩
  exact Subgroup.subset_closure ⟨m, congrArg Subtype.val hm⟩

omit [IsAlgClosed k] in
/-- Conjugation preserves two-power orders, so the elementary subgroup is
normal in the full fixed group. -/
theorem elementary_normal (S : Geometry K) (n : ℕ) :
    (graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  apply Subgroup.le_normalizer_closure_iff.mpr
  intro g _ x hx
  obtain ⟨m, hm⟩ := hx
  apply Subgroup.subset_closure
  refine ⟨m, ?_⟩
  simpa only [map_pow, map_one, MulAut.conj_apply] using
    congrArg (MulAut.conj g) hm

/-- An opposition lift with square in the fixed torus makes every torus
point a product of two involutions. The lift first has fourth power one;
injectivity of squaring on the torus then makes its square one. -/
theorem fixedTorus_le_elementary_of_opposition (S : Geometry K) (n : ℕ)
    (w : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n)
    (hw : w ^ 2 ∈ fixedTorus S n)
    (hinv : ∀ t ∈ fixedTorus S n, w * t * w⁻¹ = t⁻¹) :
    fixedTorus S n ≤
      graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n := by
  have hw4 : (w ^ 2) ^ 2 = 1 := by
    have h := hinv (w ^ 2) hw
    have heq : w ^ 2 = (w ^ 2)⁻¹ := by
      calc
        w ^ 2 = w * w ^ 2 * w⁻¹ := by group
        _ = (w ^ 2)⁻¹ := h
    calc
      (w ^ 2) ^ 2 = w ^ 2 * w ^ 2 := pow_two _
      _ = w ^ 2 * (w ^ 2)⁻¹ := by rw [← heq]
      _ = 1 := mul_inv_cancel _
  have hw2 : w ^ 2 = 1 := by
    have heq : (⟨w ^ 2, hw⟩ : fixedTorus S n) ^ 2 = 1 ^ 2 := by
      apply Subtype.ext
      simpa only [Subgroup.coe_pow, Subgroup.coe_one, one_pow] using hw4
    exact congrArg Subtype.val (fixedTorus_sq_injective S n heq)
  have hwE : w ∈ graphFieldElementarySubgroup
      S.diagram.toMulEquiv S.frobenius.onPoints n :=
    Subgroup.subset_closure ⟨1, by simpa using hw2⟩
  intro t ht
  have htw : (t * w) ^ 2 = 1 := by
    calc
      (t * w) ^ 2 = t * (w * t * w⁻¹) * w ^ 2 := by rw [pow_two]; group
      _ = t * t⁻¹ * 1 := by rw [hinv t ht, hw2]
      _ = 1 := by group
  have htwE : t * w ∈ graphFieldElementarySubgroup
      S.diagram.toMulEquiv S.frobenius.onPoints n :=
    Subgroup.subset_closure ⟨1, by simpa using htw⟩
  simpa using (graphFieldElementarySubgroup
    S.diagram.toMulEquiv S.frobenius.onPoints n).mul_mem htwE
      ((graphFieldElementarySubgroup
        S.diagram.toMulEquiv S.frobenius.onPoints n).inv_mem hwE)

/-- The characteristic-two argument at the end of Steinberg 12.4: a square
root in the fixed torus conjugates an elementary inversion representative
to its torus translate. Normality then puts that torus point in the elementary
subgroup. Existence of the inversion representative remains an explicit input. -/
theorem fixedTorus_le_elementary_of_inverting_element (S : Geometry K) (n : ℕ)
    (hn : 0 < n)
    (w : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n)
    (hw : w ∈ graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n)
    (hinv : ∀ t ∈ fixedTorus S n, w * t * w⁻¹ = t⁻¹) :
    fixedTorus S n ≤
      graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n := by
  intro t ht
  obtain ⟨a, ha⟩ := fixedTorus_square_surjective S n hn ⟨t, ht⟩
  have ha2 : (a : graphFieldFixedSubgroup S.diagram.toMulEquiv
      S.frobenius.onPoints n) ^ 2 = t := congrArg Subtype.val ha
  have hconj := (elementary_normal S n).conj_mem w hw a
  have hai := hinv a a.property
  have heq : (a : graphFieldFixedSubgroup S.diagram.toMulEquiv
      S.frobenius.onPoints n) * w * (a : graphFieldFixedSubgroup
        S.diagram.toMulEquiv S.frobenius.onPoints n)⁻¹ * w⁻¹ = t := by
    calc
      _ = (a : graphFieldFixedSubgroup S.diagram.toMulEquiv
          S.frobenius.onPoints n) * (w * (a : graphFieldFixedSubgroup
            S.diagram.toMulEquiv S.frobenius.onPoints n) * w⁻¹)⁻¹ := by group
      _ = (a : graphFieldFixedSubgroup S.diagram.toMulEquiv
          S.frobenius.onPoints n) ^ 2 := by rw [hai]; simp [pow_two]
      _ = t := ha2
  rw [← heq]
  exact (graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n).mul_mem
    hconj ((graphFieldElementarySubgroup
      S.diagram.toMulEquiv S.frobenius.onPoints n).inv_mem hw)

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
