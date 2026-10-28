module
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.Lower.Relations
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Exchanges.ShortRoots.Model
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Recovering the exact upper trace exchanges

The short2, long1 and long2 sections commute under `CommutingPairs`.
Their product therefore defines a homomorphism whose projection is injective
by the genuine six-root coordinate uniqueness. An upper collector correction
lies in this subgroup, so its projected trace formula determines it exactly
in the covering group. No vanishing of a central defect is assumed.

These coefficients feed the additivity proof for the lower short–short
exchange. Source: GLS3 §2.4.5(b), in the folded marking of `RootRelations`;
Aschbacher–Smith I.1.3 (PDF p.418).
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField.LowerNormalization.ShortPair
open RootSections RootSections.ShortPolynomial
open RadicalCoordinates.LeviCommutators RadicalCoordinates.Centers
variable {n : ℕ} {hn : 0 < n} {E : Type*} [Group E]
variable {f : E →* BinaryCarrier n hn}
local notation "P" => binaryParameters n hn
local notation "K" => ExtensionField P

/-- Recover the named commuting family from the collector's unordered pairs. -/
theorem commutingRelations (L : RootSections n hn f) (hc : CommutingPairs L) :
    L.CommutingRelations := by
  constructor
  · intro s t; exact hc 0 4 (fun _ => s, 0) (0, fun _ => t) (by decide) (by simp [interactingPair])
  · intro s t; exact hc 0 5 (fun _ => s, 0) (0, fun _ => t) (by decide) (by simp [interactingPair])
  · intro s t; exact hc 1 2 (0, fun _ => s) (fun _ => t, 0) (by decide) (by simp [interactingPair])
  · intro s t; exact hc 1 3 (0, fun _ => s) (fun _ => t, 0) (by decide) (by simp [interactingPair])
  · intro s t; exact hc 1 5 (0, fun _ => s) (0, fun _ => t) (by decide) (by simp [interactingPair])
  · intro s t; exact hc 2 4 (fun _ => s, 0) (0, fun _ => t) (by decide) (by simp [interactingPair])
  · intro s t; exact hc 2 5 (fun _ => s, 0) (0, fun _ => t) (by decide) (by simp [interactingPair])
  · intro s t; exact hc 3 4 (fun _ => s, 0) (0, fun _ => t) (by decide) (by simp [interactingPair])
  · intro s t; exact hc 3 5 (fun _ => s, 0) (0, fun _ => t) (by decide) (by simp [interactingPair])
  · intro s t; exact hc 4 5 (0, fun _ => s) (0, fun _ => t) (by decide) (by simp [interactingPair])

/-- The commuting three-root correction subgroup, with its actual coordinates. -/
def tailHom (L : RootSections n hn f) (hc : L.CommutingRelations) :
    (Multiplicative K × Multiplicative (fixedField P)) ×
      Multiplicative (fixedField P) →* E :=
  ((L.shortRoot 2).noncommCoprod (L.longRoot 1)
    (fun a b => hc.short2_long1 a.toAdd b.toAdd)).noncommCoprod (L.longRoot 2)
      (fun a b => (hc.short2_long2 a.1.toAdd b.toAdd).mul_left
        (hc.long1_long2 a.2.toAdd b.toAdd))

private theorem tail_project (L : RootSections n hn f) (hc : L.CommutingRelations)
    (s : K) (a b : fixedField P) :
    f (tailHom L hc ((.ofAdd s, .ofAdd a), .ofAdd b)) =
      baseProduct n hn (![0, 0, s], ![0, a, b]) := by
  change f (L.shortValue 2 s * L.longValue 1 a * L.longValue 2 b) = _
  have hs0 (i : Fin 3) : short P rfl i 0 = 1 := by
    rw [← L.project_short]
    exact (congrArg f (L.shortRoot i).map_one).trans f.map_one
  have hl0 (i : Fin 3) : long P rfl i 0 = 1 := by
    rw [← L.project_long]
    exact (congrArg f (L.longRoot i).map_one).trans f.map_one
  simp [baseProduct, shortValue, longValue, L.project_short, L.project_long, hs0, hl0]

/-- Projection is injective on the subgroup containing every correction word. -/
theorem tail_project_injective (L : RootSections n hn f) (hc : L.CommutingRelations) :
    Function.Injective (f.comp (tailHom L hc)) := by
  rintro ⟨⟨s, a⟩, b⟩ ⟨⟨t, c⟩, d⟩ h
  have he := baseProduct_injective n hn
    ((tail_project L hc s.toAdd a.toAdd b.toAdd).symm.trans
      (h.trans (tail_project L hc t.toAdd c.toAdd d.toAdd)))
  have hs := congrArg (fun v : PositiveParameters n hn => v.1 2) he
  have ha := congrArg (fun v : PositiveParameters n hn => v.2 1) he
  have hb := congrArg (fun v : PositiveParameters n hn => v.2 2) he
  simp only [Matrix.cons_val_two, Matrix.cons_val_one] at hs ha hb
  exact Prod.ext (Prod.ext (Multiplicative.toAdd.injective hs)
    (Multiplicative.toAdd.injective ha)) (Multiplicative.toAdd.injective hb)

theorem eq_of_tail (L : RootSections n hn f) (hc : L.CommutingRelations)
    {x y : E} (hx : x ∈ (tailHom L hc).range) (hy : y ∈ (tailHom L hc).range)
    (he : f x = f y) : x = y := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact congrArg (tailHom L hc) (tail_project_injective L hc he)

theorem tail_mem (L : RootSections n hn f) (hc : L.CommutingRelations)
    (s : K) (a b : fixedField P) :
    L.shortValue 2 s * L.longValue 1 a * L.longValue 2 b ∈ (tailHom L hc).range :=
  ⟨((.ofAdd s, .ofAdd a), .ofAdd b), rfl⟩

private theorem upper_word_mem (L : RootSections n hn f) (hc : L.CommutingRelations)
    (w : List (Fin 6 × PositiveParameters n hn))
    (hw : ∀ z ∈ w, 3 < height z.1) :
    FilteredCollection.wordProduct L.factor w ∈ (tailHom L hc).range := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨⟨i, a⟩, hi, rfl⟩ := List.mem_map.mp hx
  have hh := hw (i,a) hi
  fin_cases i <;> simp [height] at hh
  · simpa [RootSections.factor, shortValue, longValue] using tail_mem L hc 0 (a.2 1) 0
  · simpa [RootSections.factor, shortValue, longValue] using tail_mem L hc 0 0 (a.2 2)

/-- The two upper collector exchanges have exactly the genuine trace coefficients. -/
theorem upper_trace (L : RootSections n hn f) (hc : CommutingPairs L)
    (hu : UpperRelations L) (i : Fin 2) (s t : K) :
    L.shortValue (Fin.castSucc i) s * L.shortValue 2 t =
      L.shortValue 2 t * L.shortValue (Fin.castSucc i) s *
        L.longValue (Fin.succ i) (cubicTrace P (fieldFrobenius P (fieldFrobenius P s)*t)) := by
  let hC := commutingRelations L hc
  have hp : PairExchange L (if i = 0 then 0 else 2) 3 := by
    fin_cases i
    · exact hu.1
    · exact hu.2.2
  obtain ⟨w, hw, he⟩ := hp (fun _ => s, 0) (fun _ => t, 0)
  have he' : L.shortValue (Fin.castSucc i) s * L.shortValue 2 t =
      L.shortValue 2 t * L.shortValue (Fin.castSucc i) s *
        FilteredCollection.wordProduct L.factor w := by
    fin_cases i <;> simpa [RootSections.factor, shortValue] using he
  rw [he']
  congr 1
  apply eq_of_tail L hC (upper_word_mem L hC w (by
    intro z hz
    have h := hw z hz
    fin_cases i <;> simpa [height] using h))
  · fin_cases i
    · simpa [shortValue, longValue] using tail_mem L hC 0
        (cubicTrace P (fieldFrobenius P (fieldFrobenius P s)*t)) 0
    · simpa [shortValue, longValue] using tail_mem L hC 0 0
        (cubicTrace P (fieldFrobenius P (fieldFrobenius P s)*t))
  · have h := congrArg f he'
    simp only [map_mul, shortValue, longValue, L.project_short, L.project_long] at h ⊢
    have hb : short P rfl (Fin.castSucc i) s * short P rfl 2 t =
        short P rfl 2 t * short P rfl (Fin.castSucc i) s *
          long P rfl (Fin.succ i) (cubicTrace P (fieldFrobenius P (fieldFrobenius P s)*t)) := by
      fin_cases i
      · exact base_trace02 P rfl s t
      · exact base_trace12 P rfl s t
    exact mul_left_cancel (h.symm.trans hb)
end Triality.Standard.CentralCovers.TwoPrimary.SmallField.LowerNormalization.ShortPair
