module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.SplitCoverage.RootConditions
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.FixedGeometry.SplitGeneration

/-!
# Word induction for split F₄ normal forms

The positive subgroup and the negative simple root curves generate the actual
split matrix group, by generation from the two split seeds. Each negative
simple root element with nonzero parameter can also be recovered from an
actual rank-one word and two positive root elements, so `U` and the specified
normalizer-word subgroup generate the group over every coefficient field.

Local negative-simple exchange gives unrestricted `U N U` coverage by
induction on these generators. Inverses of root elements are absorbed by
negating their parameters. No exchange or restricted normal form is inferred
from generation alone. Source: GLS3 1.11.5 and 1.12.1(a),
`refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
noncomputable section

namespace ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open LargeLocalSeeds Subgroup
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem root_zero (m : ℕ) (r : F4Chevalley.Root) :
    rootGeneratorInGroup m r 0 = 1 :=
  Subtype.ext (F4Chevalley.rootCurve_zero r)

private theorem root_inv (m : ℕ) (r : F4Chevalley.Root) (t : CoefficientField m) :
    (rootGeneratorInGroup m r t)⁻¹ = rootGeneratorInGroup m r (-t) :=
  Subtype.ext (F4Chevalley.rootCurve_inv r t)

private def negativeSimpleGenerators (m : ℕ) : Set (SplitGroup m) :=
  {x | ∃ (i : Fin 4) (t : CoefficientField m),
    x = rootGeneratorInGroup m (-typeF4SimpleRootIndex i) t}

private theorem positive_negative_simple_generate (m : ℕ) :
    closure ((splitUnipotent m : Set (SplitGroup m)) ∪ negativeSimpleGenerators m) = ⊤ := by
  let H := closure ((splitUnipotent m : Set (SplitGroup m)) ∪ negativeSimpleGenerators m)
  have hs (s : Side) : splitSeed m s ≤ H := by
    apply (closure_le _).mpr
    rintro _ ⟨r, t, hr, rfl⟩
    rcases hr with hr | ⟨i, _, rfl⟩
    · exact subset_closure (Or.inl (subset_closure ⟨r, t, hr, rfl⟩))
    · exact subset_closure (Or.inr ⟨i, t, rfl⟩)
  apply top_unique
  rw [← splitSeed_sup_eq_top m]
  exact sup_le (hs .suzuki) (hs .linear)

/-- Positive root elements and the actual nonzero rank-one words generate
the split group. No field-size restriction or geometric premise is needed. -/
theorem splitUnipotent_sup_normalizerWords_eq_top (m : ℕ) :
    splitUnipotent m ⊔ splitNormalizerWords m = ⊤ := by
  let H := splitUnipotent m ⊔ splitNormalizerWords m
  have hp (i : Fin 4) (t : CoefficientField m) :
      rootGeneratorInGroup m (typeF4SimpleRootIndex i) t ∈ H :=
    mem_sup_left (subset_closure ⟨_, t,
      typeF4RootPairing_base.isPos_of_mem_support
        (typeF4RootPairing_baseEquiv i).property, rfl⟩)
  have hn (i : Fin 4) (t : CoefficientField m) :
      rootGeneratorInGroup m (-typeF4SimpleRootIndex i) t ∈ H := by
    by_cases ht : t = 0
    · rw [ht, root_zero]
      exact H.one_mem
    · let a : (CoefficientField m)ˣ := -(Units.mk0 t ht)⁻¹
      have he : rootGeneratorInGroup m (-typeF4SimpleRootIndex i) t =
          (rootGeneratorInGroup m (typeF4SimpleRootIndex i) a)⁻¹ *
            rankOneRepresentative m (typeF4SimpleRootIndex i) a *
            (rootGeneratorInGroup m (typeF4SimpleRootIndex i) a)⁻¹ := by
        simp only [rankOneRepresentative, a, inv_neg, inv_inv, Units.val_neg,
          neg_neg, Units.val_mk0]
        group
      rw [he]
      exact H.mul_mem
        (H.mul_mem (H.inv_mem (hp i a))
          (mem_sup_right (rankOneRepresentative_mem m _ a))) (H.inv_mem (hp i a))
  apply top_unique
  rw [← positive_negative_simple_generate m]
  apply (closure_le _).mpr
  rintro x (hx | ⟨i, t, rfl⟩)
  · exact mem_sup_left hx
  · exact hn i t

/-- Local negative-simple exchange extends to all words in the split group.
This supplies unrestricted coverage; collecting the right factor is separate. -/
theorem exists_unrestricted_factors_of_negativeSimpleExchange (m : ℕ)
    (hexchange : NegativeSimpleExchange m) (g : SplitGroup m) :
    ∃ u ∈ splitUnipotent m, ∃ n ∈ splitNormalizerWords m,
      ∃ v ∈ splitUnipotent m, g = u * n * v := by
  let F : SplitGroup m → Prop := fun x =>
    ∃ u ∈ splitUnipotent m, ∃ n ∈ splitNormalizerWords m,
      ∃ v ∈ splitUnipotent m, x = u * n * v
  have hpositive (u : SplitGroup m) (hu : u ∈ splitUnipotent m)
      (x : SplitGroup m) (hx : F x) : F (u * x) := by
    obtain ⟨a, ha, n, hn, c, hc, rfl⟩ := hx
    exact ⟨u * a, (splitUnipotent m).mul_mem hu ha, n, hn, c, hc, by group⟩
  have hnegative (i : Fin 4) (t : CoefficientField m)
      (x : SplitGroup m) (hx : F x) :
      F (rootGeneratorInGroup m (-typeF4SimpleRootIndex i) t * x) := by
    obtain ⟨u, hu, n, hn, v, hv, rfl⟩ := hx
    obtain ⟨a, ha, n', hn', c, hc, he⟩ := hexchange i t u hu n hn
    refine ⟨a, ha, n', hn', c * v, (splitUnipotent m).mul_mem hc hv, ?_⟩
    calc
      _ = (rootGeneratorInGroup m (-typeF4SimpleRootIndex i) t * u * n) * v := by group
      _ = a * n' * (c * v) := by rw [he, mul_assoc]
  have hg : g ∈ closure ((splitUnipotent m : Set (SplitGroup m)) ∪
      negativeSimpleGenerators m) := by
    rw [positive_negative_simple_generate]
    exact mem_top g
  change F g
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨1, (splitUnipotent m).one_mem, 1,
      (splitNormalizerWords m).one_mem, 1, (splitUnipotent m).one_mem, by simp⟩
  | mul_left x hx y _ ih =>
      rcases hx with hx | ⟨i, t, rfl⟩
      · exact hpositive x hx y ih
      · exact hnegative i t y ih
  | inv_mul_cancel x hx y _ ih =>
      rcases hx with hx | ⟨i, t, rfl⟩
      · exact hpositive x⁻¹ ((splitUnipotent m).inv_mem hx) y ih
      · rw [root_inv]
        exact hnegative i (-t) y ih

end ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
