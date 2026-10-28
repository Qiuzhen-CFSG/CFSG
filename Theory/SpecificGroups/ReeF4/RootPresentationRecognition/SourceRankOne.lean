module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.NativeRankOne
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.SimpleCoordinates

/-!
# The Suzuki descent step on the same marked source quotient

A bijective two-parameter chart on the actual negative simple root, a faithful
parametrization of the entire Cartan, and the literal local Gauss equation
suffice for two-cell word reduction in their generated subgroup. Torus
normalization follows from the existing split root geometry. The reflection
is in the original normalizer and has the specified original simple class.

This is a conditional local step: the source owner must construct these
charts and verify the finite equation. It neither assumes a map from the
Ree model nor asserts a full source-to-model comparison. In particular its
generated subgroup is the rank-one subgroup with full Cartan, not the whole
parabolic with its additional radical.

Source: GLS3 §2.4 and Steinberg §11, Lemmas 62–64; source quotient and root
conventions are those of DGS, Groups and Graphs, Theorem D, p.224, and Carter
§2.5 (`refs/KGroup/GLS3/Chapter2Ca2.tex`).
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.SourceRankOne
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2) (n : Q.tits.N)

/-- The negative of the same source simple root, using the selected literal lift. -/
def negativeRoot : Subgroup (X ⧸ Q.D) :=
  rightConjugate (simpleRoot Q split i) (n : X ⧸ Q.D)

/-- Local finite data only. No global homomorphism or normal-form premise occurs. -/
structure SuzukiData (m : ℕ) where
  chart : (CoefficientField m × CoefficientField m) ≃ negativeRoot Q split i n
  chart_zero : ((chart (0,0) : negativeRoot Q split i n) : X ⧸ Q.D) = 1
  h : TorusParameter m →* X ⧸ Q.D
  h_range : h.range = Q.tits.B ⊓ Q.tits.N
  h_injective : Function.Injective h
  reflection_class : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple i
  reflection_sq : (n : X ⧸ Q.D) * n = 1
  gauss : ∀ t u : CoefficientField m, ∀ hn : norm t u ≠ 0,
    (n : X ⧸ Q.D) * (chart (t,u) : X ⧸ Q.D) =
      (chart (negativeFirst t u, negativeSecond t u) : X ⧸ Q.D) *
        h (suzukiTau (Units.mk0 (norm t u) hn)) *
          ((n : X ⧸ Q.D) * (chart (positiveFirst t u, positiveSecond t u) : X ⧸ Q.D) * n)

/-- The source rank-one subgroup, retaining its full original Cartan. -/
def generated : Subgroup (X ⧸ Q.D) :=
  negativeRoot Q split i n ⊔ (Q.tits.B ⊓ Q.tits.N) ⊔ zpowers (n : X ⧸ Q.D)

variable {m : ℕ} (d : SuzukiData Q split i n m)

/-- The explicit finite source Gauss equation supplies the abstract descent relation. -/
theorem gauss_conjugate (t u : CoefficientField m) (hn : norm t u ≠ 0) :
    (n : X ⧸ Q.D) * (d.chart (t,u) : X ⧸ Q.D) * n =
      (d.chart (negativeFirst t u, negativeSecond t u) : X ⧸ Q.D) *
        d.h (suzukiTau (Units.mk0 (norm t u) hn)) * n *
          (d.chart (positiveFirst t u, positiveSecond t u) : X ⧸ Q.D) := by
  rw [d.gauss t u hn]
  simp only [mul_assoc, d.reflection_sq, mul_one]

include d in
/-- Arbitrary words in the actual source local generators reduce to the two cells. -/
theorem normalForm (g : X ⧸ Q.D) (hg : g ∈ generated Q split i n) :
    RankOne.NormalForm (negativeRoot Q split i n) (Q.tits.B ⊓ Q.tits.N)
      (n : X ⧸ Q.D) g := by
  apply RankOne.normalForm_of_mem _ _ _
    (torus_normalizes_rightConjugate (simpleRoot Q split i)
      (torus_normalizes_simpleRoot Q split i) n)
    (torus_normalizes n) d.reflection_sq ?_ hg
  intro x hx hx1
  obtain ⟨⟨t,u⟩, htu⟩ := d.chart.surjective ⟨x,hx⟩
  have he : (d.chart (t,u) : X ⧸ Q.D) = x := congrArg Subtype.val htu
  have htu' : t ≠ 0 ∨ u ≠ 0 := by
    by_contra! h
    exact hx1 (by rw [← he, h.1, h.2, d.chart_zero])
  have hn := norm_ne_zero t u htu'
  refine ⟨d.chart (negativeFirst t u, negativeSecond t u), (d.chart _).property,
    d.h (suzukiTau (Units.mk0 (norm t u) hn)), ?_,
    d.chart (positiveFirst t u, positiveSecond t u), (d.chart _).property, ?_⟩
  · rw [← d.h_range]
    exact ⟨_, rfl⟩
  · rw [← he]
    exact gauss_conjugate Q split i n d t u hn

/-- The root and torus factors in source word reduction have literal finite parameters. -/
theorem coordinateForm (g : X ⧸ Q.D) (hg : g ∈ generated Q split i n) :
    (∃ a : CoefficientField m × CoefficientField m, ∃ t : TorusParameter m,
      g = (d.chart a : X ⧸ Q.D) * d.h t) ∨
    ∃ a : CoefficientField m × CoefficientField m, ∃ t : TorusParameter m,
      ∃ b : CoefficientField m × CoefficientField m,
        g = (d.chart a : X ⧸ Q.D) * d.h t * n * (d.chart b : X ⧸ Q.D) := by
  have hT {t : X ⧸ Q.D} (ht : t ∈ Q.tits.B ⊓ Q.tits.N) : ∃ a, d.h a = t := by
    rw [← d.h_range] at ht
    exact ht
  rcases normalForm Q split i n d g hg with ⟨a, ha, t, ht, he⟩ |
    ⟨a, ha, t, ht, b, hb, he⟩
  · obtain ⟨u, hu⟩ := d.chart.surjective ⟨a,ha⟩
    obtain ⟨v, rfl⟩ := hT ht
    exact Or.inl ⟨u, v, he.trans (congrArg (fun z : negativeRoot Q split i n =>
      (z : X ⧸ Q.D) * d.h v) hu).symm⟩
  · obtain ⟨u, hu⟩ := d.chart.surjective ⟨a,ha⟩
    obtain ⟨v, rfl⟩ := hT ht
    obtain ⟨w, hw⟩ := d.chart.surjective ⟨b,hb⟩
    refine Or.inr ⟨u, v, w, ?_⟩
    rw [congrArg Subtype.val hu, congrArg Subtype.val hw]
    exact he

include d in
/-- These local words lie in the endpoint selected by the original simple marking. -/
theorem generated_le_endpoint :
    generated Q split i n ≤ Q.tits.standardParabolic {Q.simple i} := by
  have hn : (n : X ⧸ Q.D) ∈ Q.tits.standardParabolic {Q.simple i} :=
    Q.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
      (Q.tits.representative_mem_bruhatCell _ n d.reflection_class)
  have hB := Q.tits.B_le_standardParabolic {Q.simple i}
  apply sup_le (sup_le ?_ (inf_le_left.trans hB)) (zpowers_le.mpr hn)
  intro x hx
  have hxB := hB (split.U_le (simpleRoot_le Q split i hx))
  have he := (Q.tits.standardParabolic {Q.simple i}).mul_mem
    ((Q.tits.standardParabolic {Q.simple i}).mul_mem
      ((Q.tits.standardParabolic {Q.simple i}).inv_mem hn) hxB) hn
  change (n : X ⧸ Q.D)⁻¹ * ((n : X ⧸ Q.D)*x*(n : X ⧸ Q.D)⁻¹) * n ∈ _ at he
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using he

include d in
/-- Every collected source local word has a unique lift in its original endpoint,
under exactly `MarkedQuotient.q`, with no new quotient map. -/
theorem existsUnique_endpoint_lift (g : X ⧸ Q.D) (hg : g ∈ generated Q split i n) :
    ∃! a : P i, Q.q a = g := by
  let y : Q.tits.standardParabolic {Q.simple i} :=
    ⟨g, generated_le_endpoint Q split i n d hg⟩
  refine ⟨(Q.endpointEquiv i).symm y, ?_, ?_⟩
  · simpa only [Q.endpointEquiv_apply] using
      congrArg Subtype.val ((Q.endpointEquiv i).apply_symm_apply y)
  · intro a ha
    apply (Q.endpointEquiv i).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    simpa only [Q.endpointEquiv_apply] using ha

end ReeF4.RootPresentationRecognition.SourceRankOne
