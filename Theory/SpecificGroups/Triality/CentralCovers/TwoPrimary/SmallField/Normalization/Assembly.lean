module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.HighestLift
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Pairs

/-!
# Assembly of the five lifted folded-root exchanges

An exchange in one direction gives the reverse exchange by reversing and
inverting its correction word. Consequently the five unordered interacting
pairs, together with the ten commuting pairs, give precisely the collector's
`HigherCommutators` hypothesis. The three upper exchanges use only long-root
corrections; changing short sections centrally preserves them.

Any two systems of additive sections differ by additive maps into the literal
central kernel. This turns a constructed compatible root system into the
`CentralAdjustment` required by the smallest-field consumer.

These are conditional assembly results. They do not assert that the lifted
relations hold merely because the corresponding base identities hold.
Sources: GLS3 §2.4.5(b), §6.1; Aschbacher–Smith I.1.3 (PDF p.418).
-/

public section

open Triality.Standard
open scoped commutatorElement
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField
noncomputable section

variable {n : ℕ} {hn : 0 < n} {E : Type*} [Group E]
variable {f : E →* BinaryCarrier n hn}

/-- One ordered pair has a correction supported strictly above both heights. -/
@[expose] def PairExchange (L : RootSections n hn f) (i j : Fin 6) : Prop :=
  ∀ (a b : PositiveParameters n hn),
    ∃ correction : List (Fin 6 × PositiveParameters n hn),
      (∀ z ∈ correction, max (height i) (height j) < height z.1) ∧
      L.factor i a * L.factor j b =
        L.factor j b * L.factor i a * FilteredCollection.wordProduct L.factor correction

private theorem factor_zero (L : RootSections n hn f) (i : Fin 6) :
    L.factor i 0 = 1 := by
  fin_cases i <;> simp [RootSections.factor]

private theorem factor_neg (L : RootSections n hn f) (i : Fin 6)
    (a : PositiveParameters n hn) : L.factor i (-a) = (L.factor i a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← L.factor_add, neg_add_cancel, factor_zero]

/-- The reverse exchange needs no new lifted relation. -/
theorem PairExchange.symm {L : RootSections n hn f} {i j : Fin 6}
    (h : PairExchange L i j) : PairExchange L j i := by
  intro b a
  obtain ⟨c, hc, he⟩ := h a b
  let d := c.reverse.map (fun z => (z.1, -z.2))
  have hd : FilteredCollection.wordProduct L.factor d =
      (FilteredCollection.wordProduct L.factor c)⁻¹ := by
    simp only [d, FilteredCollection.wordProduct, List.map_map, List.map_reverse,
      Function.comp_def, factor_neg, List.prod_inv_reverse]
  refine ⟨d, ?_, ?_⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    rw [max_comm]
    exact hc w (List.mem_reverse.mp hw)
  · rw [hd, he, mul_inv_cancel_right]

/-- The three upper pairs have only long-root correction factors. -/
@[expose] def UpperRelations (L : RootSections n hn f) : Prop :=
  PairExchange L 0 3 ∧ PairExchange L 1 4 ∧ PairExchange L 2 3

/-- The two lower pairs require mixed and short-root corrections. -/
@[expose] def LowerRelations (L : RootSections n hn f) : Prop :=
  PairExchange L 0 1 ∧ PairExchange L 0 2

/-- All five interacting pairs and the ten commuting pairs supply the collector. -/
theorem higherCommutators_of_pairs (L : RootSections n hn f)
    (hcomm : CommutingPairs L) (hu : UpperRelations L) (hl : LowerRelations L) :
    L.HigherCommutators := by
  have forward (i j : Fin 6) (hij : i < j) : PairExchange L i j := by
    by_cases hi : interactingPair i j
    · simp only [interactingPair, min_eq_left hij.le, max_eq_right hij.le,
        Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hi
      rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hl.1
      · exact hl.2
      · exact hu.1
      · exact hu.2.1
      · exact hu.2.2
    · intro a b
      exact ⟨[], by simp, by simpa [FilteredCollection.wordProduct] using
        (hcomm i j a b (ne_of_lt hij) hi).eq⟩
  intro i j a b hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact forward i j h a b
  · exact (forward j i h).symm a b

private theorem same_factor_projection (L M : RootSections n hn f)
    (i : Fin 6) (a : PositiveParameters n hn) :
    f (L.factor i a) = f (M.factor i a) := by
  fin_cases i <;> simp [RootSections.factor, L.project_short, L.project_long,
    M.project_short, M.project_long]

private theorem exchange_iff_inv_commutator {x y w : E} :
    x * y = y * x * w ↔ ⁅x⁻¹, y⁻¹⁆ = w := by
  constructor
  · intro h
    calc
      ⁅x⁻¹, y⁻¹⁆ = (y * x)⁻¹ * (x * y) := by
        simp [commutatorElement_def, mul_assoc]
      _ = w := by rw [h, inv_mul_cancel_left]
  · intro h
    rw [← h, commutatorElement_def]
    group

/-- Central changes of short sections preserve any exchange whose corrections
are all long roots of height at least four. -/
theorem PairExchange.of_same_long {L M : RootSections n hn f}
    (hk : f.ker ≤ Subgroup.center E) (hlong : L.longRoot = M.longRoot)
    {i j : Fin 6} (hheight : 3 ≤ max (height i) (height j))
    (h : PairExchange L i j) : PairExchange M i j := by
  intro a b
  obtain ⟨c, hc, he⟩ := h a b
  have hw : FilteredCollection.wordProduct L.factor c =
      FilteredCollection.wordProduct M.factor c := by
    apply congrArg List.prod
    apply List.map_congr_left
    intro z hz
    have hh := hc z hz
    have hh' : 3 < height z.1 := lt_of_le_of_lt hheight hh
    rcases z with ⟨k, v⟩
    fin_cases k <;> simp [height] at hh'
    all_goals simp [RootSections.factor, hlong]
  refine ⟨c, hc, ?_⟩
  apply exchange_iff_inv_commutator.mpr
  rw [← hw, ← exchange_iff_inv_commutator.mp he]
  apply CentralExtension.commutator_eq_of_image_eq f hk
  · rw [map_inv, map_inv, same_factor_projection M L]
  · rw [map_inv, map_inv, same_factor_projection M L]

/-- The upper family survives simultaneous central changes to all short lifts. -/
theorem UpperRelations.of_same_long {L M : RootSections n hn f}
    (hk : f.ker ≤ Subgroup.center E) (hlong : L.longRoot = M.longRoot)
    (h : UpperRelations L) : UpperRelations M :=
  ⟨h.1.of_same_long hk hlong (by decide),
    h.2.1.of_same_long hk hlong (by decide), h.2.2.of_same_long hk hlong (by decide)⟩

private def sectionDifference {B A : Type*} [Group B] [Group A]
    (f : E →* B) (hk : f.ker ≤ Subgroup.center E)
    (s t : A →* E) (hp : ∀ x, f (s x) = f (t x)) : A →* f.ker where
  toFun x := ⟨(s x)⁻¹ * t x, by simp [MonoidHom.mem_ker, hp]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := by
    apply Subtype.ext
    change (s (x*y))⁻¹ * t (x*y) = ((s x)⁻¹ * t x) * ((s y)⁻¹ * t y)
    have hc : Commute ((s x)⁻¹ * t x) (s y)⁻¹ :=
      (Subgroup.mem_center_iff.mp (hk (by simp [MonoidHom.mem_ker, hp])) _).symm
    simp only [map_mul, mul_inv_rev]
    calc
      (s y)⁻¹ * (s x)⁻¹ * (t x * t y) =
          (s y)⁻¹ * ((s x)⁻¹ * t x) * t y := by group
      _ = ((s x)⁻¹ * t x) * (s y)⁻¹ * t y := by rw [hc.eq]
      _ = _ := by group

/-- The additive central difference of two marked root systems. -/
def adjustmentBetween (hk : f.ker ≤ Subgroup.center E)
    (L M : RootSections n hn f) : CentralAdjustment f where
  shortChange i := sectionDifference f hk (L.shortRoot i) (M.shortRoot i)
    (fun x => (L.project_short i x.toAdd).trans (M.project_short i x.toAdd).symm)
  longChange i := sectionDifference f hk (L.longRoot i) (M.longRoot i)
    (fun x => (L.project_long i x.toAdd).trans (M.project_long i x.toAdd).symm)

/-- Every marked additive root system is a permissible central adjustment. -/
theorem adjustmentBetween_adjusted (hk : f.ker ≤ Subgroup.center E)
    (L M : RootSections n hn f) : (adjustmentBetween hk L M).adjusted hk L = M := by
  have hs : ((adjustmentBetween hk L M).adjusted hk L).shortRoot = M.shortRoot := by
    funext i
    apply MonoidHom.ext
    intro x
    rw [show x = Multiplicative.ofAdd x.toAdd from rfl, CentralAdjustment.adjusted_short]
    change L.shortRoot i x * ((L.shortRoot i x)⁻¹ * M.shortRoot i x) = _
    exact mul_inv_cancel_left _ _
  have hl : ((adjustmentBetween hk L M).adjusted hk L).longRoot = M.longRoot := by
    funext i
    apply MonoidHom.ext
    intro x
    rw [show x = Multiplicative.ofAdd x.toAdd from rfl, CentralAdjustment.adjusted_long]
    change L.longRoot i x * ((L.longRoot i x)⁻¹ * M.longRoot i x) = _
    exact mul_inv_cancel_left _ _
  generalize (adjustmentBetween hk L M).adjusted hk L = N at hs hl ⊢
  cases N
  cases M
  cases hs
  cases hl
  rfl

end
end Triality.Standard.CentralCovers.TwoPrimary.SmallField
