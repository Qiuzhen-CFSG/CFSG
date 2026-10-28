module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.CentralHigherGeneration.Scalars
public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.TorusMotion.Scalars
public import Theory.GroupTheory.FilteredCollection

/-!
# Collection from map-free positive triality relations

Six additive root maps, over the actual cubic extension and its Frobenius
fixed field, satisfy fifteen explicit exchange equations. Every word in
these roots collects in the order A, B, C, D, E, F. Consequently their
subgroup closure is exactly the range of that six-factor product.
No projection to a triality model, injectivity or group order is an input.

The filtered exchange calculation adapts the central-cover calculation in
`CentralCovers/TwoPrimary/LargeFields/Exchanges/Collection.lean`, removing its
source projection. The collector is `FilteredCollection`; the strict heights
make correction words terminate. This is the positive part of a presentation,
not yet the signed-root Bruhat theorem.

Source: GLS3 2.4.5(b), with the literal orbit origins (0,1,2), (4,5,6),
(7,8,9) of `LeviCommutators.FoldedRoots`, rather than the differently
parametrized third short root in the GLS3 footnote.
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.RootPresentationRecognition
open Parabolics PositiveCoordinates RadicalCoordinates.LeviCommutators RadicalCoordinates.Centers
variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn

abbrev PositiveParameters := OrbitParameters P

/-- Six additive root maps. There is no ambient model map in this data. -/
structure PositiveRoots (Y : Type*) [Group Y] where
  shortRoot : Fin 3 → Multiplicative (ExtensionField P) →* Y
  longRoot : Fin 3 → Multiplicative (fixedField P) →* Y

/-- Relative heights in the published positive product order. -/
def height : Fin 6 → ℕ := ![1, 1, 2, 3, 4, 5]

namespace PositiveRoots
variable {n hn} {E : Type*} [Group E]
/-- A common parameter space for the collector; each factor uses only its
own one of the six coordinates. -/
def factor (L : PositiveRoots n hn E) (i : Fin 6) (v : PositiveParameters n hn) : E :=
  ![L.shortRoot 0 (.ofAdd (v.1 0)), L.longRoot 0 (.ofAdd (v.2 0)),
    L.shortRoot 1 (.ofAdd (v.1 1)), L.shortRoot 2 (.ofAdd (v.1 2)),
    L.longRoot 1 (.ofAdd (v.2 1)), L.longRoot 2 (.ofAdd (v.2 2))] i

/-- The ordered product of the six lifted folded roots. -/
def product (L : PositiveRoots n hn E) (v : PositiveParameters n hn) : E :=
  (List.ofFn fun i : Fin 6 => L.factor i v).prod

theorem factor_add (L : PositiveRoots n hn E) (i : Fin 6) (v w : PositiveParameters n hn) :
    L.factor i (v + w) = L.factor i v * L.factor i w := by
  fin_cases i <;> simp [factor, ← map_mul, ← ofAdd_add]

theorem product_zero (L : PositiveRoots n hn E) : L.product 0 = 1 := by
  simp [product, factor, List.ofFn_succ]

/-- Exchanges with correction roots strictly above both original heights. -/
def HigherCommutators (L : PositiveRoots n hn E) : Prop :=
  ∀ (i j : Fin 6) (a b : PositiveParameters n hn), i ≠ j →
    ∃ correction : List (Fin 6 × PositiveParameters n hn),
      (∀ z ∈ correction, max (height i) (height j) < height z.1) ∧
      L.factor i a * L.factor j b =
        L.factor j b * L.factor i a * FilteredCollection.wordProduct L.factor correction

abbrev shortValue (L : PositiveRoots n hn E) (i : Fin 3) (t : ExtensionField P) : E :=
  L.shortRoot i (.ofAdd t)

abbrev longValue (L : PositiveRoots n hn E) (i : Fin 3) (t : fixedField P) : E :=
  L.longRoot i (.ofAdd t)

/-- The ten positive folded-root pairs with no root-sum correction. -/
structure CommutingRelations (L : PositiveRoots n hn E) : Prop where
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
structure ShortExchangeRelations (L : PositiveRoots n hn E) : Prop where
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
def LongExchangeRelation (L : PositiveRoots n hn E) : Prop :=
  ∀ s t, L.longValue 0 s * L.longValue 1 t =
    L.longValue 1 t * L.longValue 0 s * L.longValue 2 (s*t)

private def shortParameters (i : Fin 3) (t : ExtensionField P) : PositiveParameters n hn :=
  (Function.update 0 i t, 0)

private def longParameters (i : Fin 3) (t : fixedField P) : PositiveParameters n hn :=
  (0, Function.update 0 i t)

private theorem factor_neg (L : PositiveRoots n hn E) (i : Fin 6) (a : PositiveParameters n hn) :
    L.factor i (-a) = (L.factor i a)⁻¹ := by
  fin_cases i <;> simp [factor, ← map_inv]

private theorem inverse_word (L : PositiveRoots n hn E)
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
def ExchangeAt (L : PositiveRoots n hn E) (i j : Fin 6) : Prop :=
  ∀ a b : PositiveParameters n hn,
    ∃ correction : List (Fin 6 × PositiveParameters n hn),
      (∀ z ∈ correction, max (height i) (height j) < height z.1) ∧
      L.factor i a * L.factor j b =
        L.factor j b * L.factor i a * FilteredCollection.wordProduct L.factor correction

/-- No new relation is needed for the reversed order. -/
theorem ExchangeAt.symm (L : PositiveRoots n hn E) {i j : Fin 6}
    (h : L.ExchangeAt i j) : L.ExchangeAt j i := by
  intro a b
  obtain ⟨w, hw, he⟩ := h b a
  refine ⟨w.reverse.map (fun z => (z.1, -z.2)), ?_, ?_⟩
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    simpa only [max_comm] using hw y (List.mem_reverse.mp hy)
  · rw [inverse_word]
    exact (eq_mul_inv_iff_mul_eq.mpr he.symm)

private theorem exchangeAt_of_commute (L : PositiveRoots n hn E) (i j : Fin 6)
    (h : ∀ a b, Commute (L.factor i a) (L.factor j b)) : L.ExchangeAt i j := by
  intro a b
  exact ⟨[], by simp, by simpa [FilteredCollection.wordProduct] using (h a b).eq⟩

/-- All fifteen forward relations imply every ordered exchange, including
reversed exchanges, with the original strict-height condition. -/
theorem higherCommutators_of_relations (L : PositiveRoots n hn E)
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

private def diagonal (a : Fin 6 → PositiveParameters n hn) : PositiveParameters n hn :=
  (![ (a 0).1 0, (a 2).1 1, (a 3).1 2],
    ![ (a 1).2 0, (a 4).2 1, (a 5).2 2])

private lemma diagonal_product (L : PositiveRoots n hn E) (a : Fin 6 → PositiveParameters n hn) :
    ((List.finRange 6).map fun i => L.factor i (a i)).prod = L.product (diagonal a) := by
  rw [← List.ofFn_eq_map]
  simp [product, factor, diagonal, List.ofFn_succ]

/-- Local higher-root corrections suffice to collect every lifted positive word. -/
theorem exists_collected_product (L : PositiveRoots n hn E) (hL : L.HigherCommutators)
    (word : List (Fin 6 × PositiveParameters n hn)) :
    ∃ v : PositiveParameters n hn, FilteredCollection.wordProduct L.factor word = L.product v := by
  obtain ⟨a, ha⟩ := FilteredCollection.filteredCollection_exists_params height L.factor
    (List.finRange 6) (List.nodup_finRange 6) 6
    (by intro i _; fin_cases i <;> decide)
    (fun i a b => (L.factor_add i a b).symm)
    (by
      intro i j a b _ _ hij
      obtain ⟨c, hc, he⟩ := hL i j a b hij
      exact ⟨c, fun z hz => ⟨List.mem_finRange _, hc z hz⟩, he⟩)
    word (fun z _ => List.mem_finRange _)
  exact ⟨diagonal a, ha.trans (L.diagonal_product a)⟩

/-- The collected products are closed under multiplication. -/
theorem product_mul_exists (L : PositiveRoots n hn E) (hL : L.HigherCommutators)
    (a b : PositiveParameters n hn) : ∃ v, L.product a * L.product b = L.product v := by
  obtain ⟨v, hv⟩ := L.exists_collected_product hL
    ((List.ofFn fun i : Fin 6 => (i, a)) ++ (List.ofFn fun i : Fin 6 => (i, b)))
  refine ⟨v, ?_⟩
  simpa only [FilteredCollection.wordProduct, List.map_append, List.prod_append,
    List.map_ofFn, Function.comp_def, product] using hv

/-- All fifteen positive exchange equations, with literal Frobenius coefficients. -/
structure Relations (L : PositiveRoots n hn E) : Prop where
  commuting : L.CommutingRelations
  shortExchange : L.ShortExchangeRelations
  longExchange : L.LongExchangeRelation

theorem Relations.higher {L : PositiveRoots n hn E} (h : L.Relations) :
    L.HigherCommutators :=
  L.higherCommutators_of_relations h.commuting h.shortExchange h.longExchange

/-- Pair two systems of roots over the same literal scalar fields. -/
def pair {F : Type*} [Group F] (L : PositiveRoots n hn E) (M : PositiveRoots n hn F) :
    PositiveRoots n hn (E × F) where
  shortRoot i := (L.shortRoot i).prod (M.shortRoot i)
  longRoot i := (L.longRoot i).prod (M.longRoot i)

@[simp] theorem pair_factor {F : Type*} [Group F]
    (L : PositiveRoots n hn E) (M : PositiveRoots n hn F)
    (i : Fin 6) (a : PositiveParameters n hn) :
    (L.pair M).factor i a = (L.factor i a, M.factor i a) := by
  fin_cases i <;> rfl

@[simp] theorem pair_product {F : Type*} [Group F]
    (L : PositiveRoots n hn E) (M : PositiveRoots n hn F) (a : PositiveParameters n hn) :
    (L.pair M).product a = (L.product a, M.product a) := by
  simp [product, List.ofFn_succ, pair_factor]

/-- The explicit coefficients agree in both components, so all relations pair. -/
theorem pair_relations {F : Type*} [Group F]
    {L : PositiveRoots n hn E} {M : PositiveRoots n hn F}
    (hL : L.Relations) (hM : M.Relations) : (L.pair M).Relations where
  commuting := {
    short0_long1 s t := (hL.commuting.short0_long1 s t).prod (hM.commuting.short0_long1 s t)
    short0_long2 s t := (hL.commuting.short0_long2 s t).prod (hM.commuting.short0_long2 s t)
    long0_short1 s t := (hL.commuting.long0_short1 s t).prod (hM.commuting.long0_short1 s t)
    long0_short2 s t := (hL.commuting.long0_short2 s t).prod (hM.commuting.long0_short2 s t)
    long0_long2 s t := (hL.commuting.long0_long2 s t).prod (hM.commuting.long0_long2 s t)
    short1_long1 s t := (hL.commuting.short1_long1 s t).prod (hM.commuting.short1_long1 s t)
    short1_long2 s t := (hL.commuting.short1_long2 s t).prod (hM.commuting.short1_long2 s t)
    short2_long1 s t := (hL.commuting.short2_long1 s t).prod (hM.commuting.short2_long1 s t)
    short2_long2 s t := (hL.commuting.short2_long2 s t).prod (hM.commuting.short2_long2 s t)
    long1_long2 s t := (hL.commuting.long1_long2 s t).prod (hM.commuting.long1_long2 s t)
  }
  shortExchange := {
    short0_long0 s t := Prod.ext (hL.shortExchange.short0_long0 s t) (hM.shortExchange.short0_long0 s t)
    short0_short1 s t := Prod.ext (hL.shortExchange.short0_short1 s t) (hM.shortExchange.short0_short1 s t)
    short0_short2 s t := Prod.ext (hL.shortExchange.short0_short2 s t) (hM.shortExchange.short0_short2 s t)
    short1_short2 s t := Prod.ext (hL.shortExchange.short1_short2 s t) (hM.shortExchange.short1_short2 s t)
  }
  longExchange s t := Prod.ext (hL.longExchange s t) (hM.longExchange s t)

/-- Collection chooses common product coordinates in two realizations.
This allows comparison with the native positive normal form without presupposing
any homomorphism between the realizations. -/
theorem common_product {F : Type*} [Group F]
    {L : PositiveRoots n hn E} {M : PositiveRoots n hn F}
    (hL : L.Relations) (hM : M.Relations) (a b : PositiveParameters n hn) :
    ∃ v, L.product a * L.product b = L.product v ∧
      M.product a * M.product b = M.product v := by
  obtain ⟨v, hv⟩ := (L.pair M).product_mul_exists (pair_relations hL hM).higher a b
  simp only [pair_product, Prod.mk_mul_mk, Prod.mk.injEq] at hv
  exact ⟨v, hv⟩

/-- The subgroup generated by the six positive root ranges. -/
def positiveClosure (L : PositiveRoots n hn E) : Subgroup E :=
  Subgroup.closure (Set.range fun z : Fin 6 × PositiveParameters n hn => L.factor z.1 z.2)

private theorem product_mem (L : PositiveRoots n hn E) (a : PositiveParameters n hn) :
    L.product a ∈ L.positiveClosure := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  exact Subgroup.subset_closure ⟨(i, a), rfl⟩

/-- Positive collection includes inverses, so it describes the whole subgroup. -/
theorem mem_positiveClosure_iff (L : PositiveRoots n hn E) (h : L.Relations) (g : E) :
    g ∈ L.positiveClosure ↔ ∃ a, L.product a = g := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
        obtain ⟨⟨i, a⟩, rfl⟩ := hg
        obtain ⟨v, hv⟩ := L.exists_collected_product h.higher [(i, a)]
        have hv' : L.factor i a = L.product v := by
          simpa [FilteredCollection.wordProduct] using hv
        exact ⟨v, hv'.symm⟩
    | one => exact ⟨0, L.product_zero⟩
    | mul g k _ _ hg hk =>
        obtain ⟨a, rfl⟩ := hg
        obtain ⟨b, rfl⟩ := hk
        obtain ⟨v, hv⟩ := L.product_mul_exists h.higher a b
        exact ⟨v, hv.symm⟩
    | inv g _ hg =>
        obtain ⟨a, rfl⟩ := hg
        let w := List.ofFn fun i : Fin 6 => (i, a)
        obtain ⟨v, hv⟩ := L.exists_collected_product h.higher
          (w.reverse.map fun z => (z.1, -z.2))
        rw [L.inverse_word] at hv
        exact ⟨v, hv.symm⟩
  · rintro ⟨a, rfl⟩
    exact L.product_mem a

end PositiveRoots
end Triality.Standard.RootPresentationRecognition
