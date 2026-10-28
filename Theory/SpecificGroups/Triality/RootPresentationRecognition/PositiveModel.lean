module

public import Theory.SpecificGroups.Triality.RootPresentationRecognition.PositiveCollection
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Exchanges.ShortRoots.Model

/-!
# Verification of the positive presentation on genuine binary triality

All fifteen relations of the map-free positive presentation hold on
`Standard.BinaryCarrier`. The ten commuting pairs are checked directly on
D₄ roots, without large-field or central-cover assumptions. The five remaining
relations are the proved polynomial exchanges in the same orbit marking.
The resulting six-factor product is the actual positive-coordinate bijection,
including the base fields of orders two and four.

Source: GLS3 2.4.5, in the orbit order of `LeviCommutators.FoldedRoots`.
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.RootPresentationRecognition
open Parabolics PositiveCoordinates PositiveCoordinates.SumExchangeData
open RadicalCoordinates.LeviCommutators RadicalCoordinates.Centers
open CentralCovers.TwoPrimary

/-- The native positive roots in the actual elementary central quotient. -/
def nativePositiveRoots (n : ℕ) (hn : 0 < n) : PositiveRoots n hn (BinaryCarrier n hn) where
  shortRoot := baseShortHom n hn
  longRoot := baseLongHom n hn

private theorem native_short_long_commute (P : Parameters) (hp : P.prime = 2)
    (i j : Fin 3)
    (hne : ∀ k, shortPosition i k ≠ longPosition j)
    (hns : ∀ k l, (shortPosition i k, longPosition j, l) ∉ sumTriples)
    (s : ExtensionField P) (t : fixedField P) :
    Commute (short P hp i s) (long P hp j t) := by
  have hc (k : Fin 3) (u : ExtensionField P) :
      Commute (curve P (shortPosition i k) u) (curve P (longPosition j) t.val) := by
    apply nonsumCommute_parameters P _ _ (hne k)
    rintro ⟨l, hl⟩
    exact hns k l ((mem_sumTriples_iff _ _ l).mpr ((root_sum_iff _ _ l).mp hl))
  show short P hp i s * long P hp j t = long P hp j t * short P hp i s
  simp only [short, long, ← map_mul]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, shortElementary_val, longElementary_val]
  exact (((hc 0 s).mul_left (hc 1 _)).mul_left (hc 2 _)).eq

private theorem native_long_long_commute (P : Parameters) (hp : P.prime = 2)
    (i j : Fin 3) (hne : longPosition i ≠ longPosition j)
    (hns : ∀ l, (longPosition i, longPosition j, l) ∉ sumTriples)
    (s t : fixedField P) : Commute (long P hp i s) (long P hp j t) := by
  show long P hp i s * long P hp j t = long P hp j t * long P hp i s
  simp only [long, ← map_mul]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, longElementary_val, longSplit]
  apply Commute.eq
  apply nonsumCommute_parameters P _ _ hne
  rintro ⟨l, hl⟩
  exact hns l ((mem_sumTriples_iff _ _ l).mpr ((root_sum_iff _ _ l).mp hl))

/-- All ten noninteracting positive pairs, over every binary field. -/
theorem native_commuting (n : ℕ) (hn : 0 < n) :
    (nativePositiveRoots n hn).CommutingRelations where
  short0_long1 := native_short_long_commute _ rfl 0 1 (by decide) (by decide)
  short0_long2 := native_short_long_commute _ rfl 0 2 (by decide) (by decide)
  long0_short1 s t := (native_short_long_commute _ rfl 1 0 (by decide) (by decide) t s).symm
  long0_short2 s t := (native_short_long_commute _ rfl 2 0 (by decide) (by decide) t s).symm
  long0_long2 := native_long_long_commute _ rfl 0 2 (by decide) (by decide)
  short1_long1 := native_short_long_commute _ rfl 1 1 (by decide) (by decide)
  short1_long2 := native_short_long_commute _ rfl 1 2 (by decide) (by decide)
  short2_long1 := native_short_long_commute _ rfl 2 1 (by decide) (by decide)
  short2_long2 := native_short_long_commute _ rfl 2 2 (by decide) (by decide)
  long1_long2 := native_long_long_commute _ rfl 1 2 (by decide) (by decide)

/-- The four short-root exchanges use the literal Frobenius and fixed-field inclusion. -/
theorem native_shortExchange (n : ℕ) (hn : 0 < n) :
    (nativePositiveRoots n hn).ShortExchangeRelations where
  short0_long0 := RootSections.ShortPolynomial.base_mixed _ rfl
  short0_short1 := short_zero_one_exchange _ rfl
  short0_short2 := RootSections.ShortPolynomial.base_trace02 _ rfl
  short1_short2 := RootSections.ShortPolynomial.base_trace12 _ rfl

/-- The map-free relation contract is realized on the genuine carrier. -/
theorem native_relations (n : ℕ) (hn : 0 < n) :
    (nativePositiveRoots n hn).Relations where
  commuting := native_commuting n hn
  shortExchange := native_shortExchange n hn
  longExchange := long_zero_one_exchange _ rfl

/-- The collector's product is exactly the existing positive-coordinate map. -/
theorem native_product (n : ℕ) (hn : 0 < n) (v : PositiveParameters n hn) :
    (nativePositiveRoots n hn).product v = baseProduct n hn v := by
  simp [PositiveRoots.product, PositiveRoots.factor, nativePositiveRoots,
    baseShortHom, baseLongHom, baseProduct, List.ofFn_succ, mul_assoc]

/-- No quotient or root-origin change occurs in the comparison with normal coordinates. -/
theorem native_product_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (nativePositiveRoots n hn).product := by
  intro v w h
  apply baseProduct_injective n hn
  exact (native_product n hn v).symm.trans (h.trans (native_product n hn w))

/-- The positive root closure is the full native unipotent subgroup. -/
theorem native_positiveClosure (n : ℕ) (hn : 0 < n) :
    (nativePositiveRoots n hn).positiveClosure = unipotent (binaryParameters n hn) := by
  ext g
  rw [PositiveRoots.mem_positiveClosure_iff _ (native_relations n hn)]
  simp only [native_product, ← positiveEquiv_val]
  constructor
  · rintro ⟨v, rfl⟩
    exact (positiveEquiv n hn v).property
  · intro hg
    obtain ⟨v, hv⟩ := (positiveEquiv n hn).surjective ⟨g, hg⟩
    exact ⟨v, congrArg Subtype.val hv⟩

end Triality.Standard.RootPresentationRecognition
