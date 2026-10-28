module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Normalization
public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.CentralHigherGeneration.Exchange

/-!
# Exchange interfaces for the six positive triality roots

The ten noninteracting pairs, the four short-root exchanges, and the long-root
A₂ exchange imply the filtered collection relations in both directions.
The coefficients use the actual Frobenius marking (0,1,2), (4,5,6), (7,8,9).
Reversing an exchange reverses and negates its correction word, so every
factor still lies strictly above both original heights.

These are conditional collection results. The relations in the cover must
be established separately; projection to the carrier does not suffice.
Sources: GLS3 §2.4, especially 2.4.5(b), and §6.1; Aschbacher–Smith I.1.3.
-/

@[expose] public section
namespace Triality.Standard.CentralCovers.TwoPrimary
open Parabolics RadicalCoordinates.LeviCommutators RadicalCoordinates.Centers
noncomputable section
variable {n : ℕ} {hn : 0 < n} {E : Type*} [Group E]
variable {f : E →* BinaryCarrier n hn}
local notation "P" => binaryParameters n hn

namespace RootSections

abbrev shortValue (L : RootSections n hn f) (i : Fin 3) (t : ExtensionField P) : E :=
  L.shortRoot i (.ofAdd t)

abbrev longValue (L : RootSections n hn f) (i : Fin 3) (t : fixedField P) : E :=
  L.longRoot i (.ofAdd t)

/-- The ten positive folded-root pairs with no root-sum correction. -/
structure CommutingRelations (L : RootSections n hn f) : Prop where
  short0_long1 : ∀ s t, Commute (L.shortValue 0 s) (L.longValue 1 t)
  short0_long2 : ∀ s t, Commute (L.shortValue 0 s) (L.longValue 2 t)
  long0_short1 : ∀ s t, Commute (L.longValue 0 s) (L.shortValue 1 t)
  long0_short2 : ∀ s t, Commute (L.longValue 0 s) (L.shortValue 2 t)
  long0_long2 : ∀ s t, Commute (L.longValue 0 s) (L.longValue 2 t)
  short1_long1 : ∀ s t, Commute (L.shortValue 1 s) (L.longValue 1 t)
  short1_long2 : ∀ s t, Commute (L.shortValue 1 s) (L.longValue 2 t)
  short2_long1 : ∀ s t, Commute (L.shortValue 2 s) (L.longValue 1 t)
  short2_long2 : ∀ s t, Commute (L.shortValue 2 s) (L.longValue 2 t)
  long1_long2 : ∀ s t, Commute (L.longValue 1 s) (L.longValue 2 t)

/-- The four interacting pairs involving short roots, with the literal
triality coefficients in the published root marking. -/
structure ShortExchangeRelations (L : RootSections n hn f) : Prop where
  short0_long0 : ∀ s t,
    L.shortValue 0 s * L.longValue 0 t =
      L.longValue 0 t * L.shortValue 0 s * L.shortValue 1 (s*t.val) *
        L.shortValue 2 (s * fieldFrobenius P s * t.val) * L.longValue 1 (cubicNorm P s * t)
  short0_short1 : ∀ s t,
    L.shortValue 0 s * L.shortValue 1 t =
      L.shortValue 1 t * L.shortValue 0 s * L.shortValue 2 (higherCoefficient P s t) *
        L.longValue 1 (cubicTrace P (s * fieldFrobenius P s *
          fieldFrobenius P (fieldFrobenius P t))) *
        L.longValue 2 (cubicTrace P (s * fieldFrobenius P t *
          fieldFrobenius P (fieldFrobenius P t)))
  short0_short2 : ∀ s t,
    L.shortValue 0 s * L.shortValue 2 t =
      L.shortValue 2 t * L.shortValue 0 s *
        L.longValue 1 (cubicTrace P (fieldFrobenius P (fieldFrobenius P s) * t))
  short1_short2 : ∀ s t,
    L.shortValue 1 s * L.shortValue 2 t =
      L.shortValue 2 t * L.shortValue 1 s *
        L.longValue 2 (cubicTrace P (fieldFrobenius P (fieldFrobenius P s) * t))

/-- The remaining interacting pair is the long-root A₂ relation. -/
def LongExchangeRelation (L : RootSections n hn f) : Prop :=
  ∀ s t, L.longValue 0 s * L.longValue 1 t =
    L.longValue 1 t * L.longValue 0 s * L.longValue 2 (s*t)

private def shortParameters (i : Fin 3) (t : ExtensionField P) : PositiveParameters n hn :=
  (Function.update 0 i t, 0)

private def longParameters (i : Fin 3) (t : fixedField P) : PositiveParameters n hn :=
  (0, Function.update 0 i t)

private theorem factor_neg (L : RootSections n hn f) (i : Fin 6) (a : PositiveParameters n hn) :
    L.factor i (-a) = (L.factor i a)⁻¹ := by
  fin_cases i <;> simp [factor, ← map_inv]

private theorem inverse_word (L : RootSections n hn f)
    (w : List (Fin 6 × PositiveParameters n hn)) :
    FilteredCollection.wordProduct L.factor (w.reverse.map fun z => (z.1, -z.2)) =
      (FilteredCollection.wordProduct L.factor w)⁻¹ := by
  induction w with
  | nil => simp [FilteredCollection.wordProduct]
  | cons a w ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      FilteredCollection.wordProduct, List.prod_append, List.prod_cons, List.prod_nil,
      mul_one, mul_inv_rev] at ih ⊢
    rw [ih, factor_neg]

/-- A single ordered pair of roots has a higher correction word. -/
def ExchangeAt (L : RootSections n hn f) (i j : Fin 6) : Prop :=
  ∀ a b : PositiveParameters n hn,
    ∃ correction : List (Fin 6 × PositiveParameters n hn),
      (∀ z ∈ correction, max (height i) (height j) < height z.1) ∧
      L.factor i a * L.factor j b =
        L.factor j b * L.factor i a * FilteredCollection.wordProduct L.factor correction

/-- No new relation is needed for the reversed order. -/
theorem ExchangeAt.symm (L : RootSections n hn f) {i j : Fin 6}
    (h : L.ExchangeAt i j) : L.ExchangeAt j i := by
  intro a b
  obtain ⟨w, hw, he⟩ := h b a
  refine ⟨w.reverse.map (fun z => (z.1, -z.2)), ?_, ?_⟩
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    simpa only [max_comm] using hw y (List.mem_reverse.mp hy)
  · rw [inverse_word]
    exact (eq_mul_inv_iff_mul_eq.mpr he.symm)

private theorem exchangeAt_of_commute (L : RootSections n hn f) (i j : Fin 6)
    (h : ∀ a b, Commute (L.factor i a) (L.factor j b)) : L.ExchangeAt i j := by
  intro a b
  exact ⟨[], by simp, by simpa [FilteredCollection.wordProduct] using (h a b).eq⟩

/-- All fifteen forward relations imply every ordered exchange, including
reversed exchanges, with the original strict-height condition. -/
theorem higherCommutators_of_relations (L : RootSections n hn f)
    (hC : L.CommutingRelations) (hS : L.ShortExchangeRelations)
    (hA : L.LongExchangeRelation) : L.HigherCommutators := by
  have hfwd (i j : Fin 6) (hij : i < j) : L.ExchangeAt i j := by
    fin_cases i <;> fin_cases j <;> simp only [Fin.lt_def] at hij <;> norm_num at hij
    · intro a b
      refine ⟨[(2, shortParameters 1 (a.1 0 * (b.2 0).val)),
        (3, shortParameters 2 (a.1 0 * fieldFrobenius P (a.1 0) * (b.2 0).val)),
        (4, longParameters 1 (cubicNorm P (a.1 0) * b.2 0))], ?_, ?_⟩
      · simp [height]
      · simpa [factor, FilteredCollection.wordProduct, shortParameters, longParameters,
          mul_assoc] using hS.short0_long0 (a.1 0) (b.2 0)
    · intro a b
      refine ⟨[(3, shortParameters 2 (higherCoefficient P (a.1 0) (b.1 1))),
        (4, longParameters 1 (cubicTrace P (a.1 0 * fieldFrobenius P (a.1 0) *
          fieldFrobenius P (fieldFrobenius P (b.1 1))))),
        (5, longParameters 2 (cubicTrace P (a.1 0 * fieldFrobenius P (b.1 1) *
          fieldFrobenius P (fieldFrobenius P (b.1 1)))))], ?_, ?_⟩
      · simp [height]
      · simpa [factor, FilteredCollection.wordProduct, shortParameters, longParameters,
          mul_assoc] using hS.short0_short1 (a.1 0) (b.1 1)
    · intro a b
      refine ⟨[(4, longParameters 1 (cubicTrace P
        (fieldFrobenius P (fieldFrobenius P (a.1 0)) * b.1 2)))], ?_, ?_⟩
      · simp [height]
      · simpa [factor, FilteredCollection.wordProduct, longParameters] using
          hS.short0_short2 (a.1 0) (b.1 2)
    · exact exchangeAt_of_commute L 0 4 (fun a b => hC.short0_long1 (a.1 0) (b.2 1))
    · exact exchangeAt_of_commute L 0 5 (fun a b => hC.short0_long2 (a.1 0) (b.2 2))
    · exact exchangeAt_of_commute L 1 2 (fun a b => hC.long0_short1 (a.2 0) (b.1 1))
    · exact exchangeAt_of_commute L 1 3 (fun a b => hC.long0_short2 (a.2 0) (b.1 2))
    · intro a b
      refine ⟨[(5, longParameters 2 (a.2 0 * b.2 1))], ?_, ?_⟩
      · simp [height]
      · simpa [factor, FilteredCollection.wordProduct, longParameters] using hA (a.2 0) (b.2 1)
    · exact exchangeAt_of_commute L 1 5 (fun a b => hC.long0_long2 (a.2 0) (b.2 2))
    · intro a b
      refine ⟨[(5, longParameters 2 (cubicTrace P
        (fieldFrobenius P (fieldFrobenius P (a.1 1)) * b.1 2)))], ?_, ?_⟩
      · simp [height]
      · simpa [factor, FilteredCollection.wordProduct, longParameters] using
          hS.short1_short2 (a.1 1) (b.1 2)
    · exact exchangeAt_of_commute L 2 4 (fun a b => hC.short1_long1 (a.1 1) (b.2 1))
    · exact exchangeAt_of_commute L 2 5 (fun a b => hC.short1_long2 (a.1 1) (b.2 2))
    · exact exchangeAt_of_commute L 3 4 (fun a b => hC.short2_long1 (a.1 2) (b.2 1))
    · exact exchangeAt_of_commute L 3 5 (fun a b => hC.short2_long2 (a.1 2) (b.2 2))
    · exact exchangeAt_of_commute L 4 5 (fun a b => hC.long1_long2 (a.2 1) (b.2 2))
  intro i j a b hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hfwd i j h a b
  · exact ExchangeAt.symm L (hfwd j i h) a b

/-- Apply the relations to the literal inclusion of the positive subgroup. -/
theorem exists_unipotent_section_of_relations (L : RootSections n hn f)
    (hC : L.CommutingRelations) (hS : L.ShortExchangeRelations)
    (hA : L.LongExchangeRelation) :
    ∃ s : unipotent P →* E, f.comp s = (unipotent P).subtype :=
  L.exists_unipotent_section (L.higherCommutators_of_relations hC hS hA)

end RootSections
end
end Triality.Standard.CentralCovers.TwoPrimary
