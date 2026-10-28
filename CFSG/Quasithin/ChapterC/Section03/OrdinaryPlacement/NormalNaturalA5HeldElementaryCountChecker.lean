module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryNative

/-!
# Product-sensitive finite certificates for native Held class counts

Besides commutation, an elementary subgroup is closed under multiplication.
A branch on v therefore includes or excludes its whole coset modulo the
already forced subgroup. The checker records lower and upper membership
bounds and proves every accepted count for the unchanged finite subgroup.
Source: Aschbacher--Smith 12.7.5, printed p.840.
-/

@[expose] public section
namespace Held.OrdinaryElementary.NativeCoverage

def marked (v : Fin 192) : Bool := classA (vertexIndex v)
def markedCount (s : Finset (Fin 192)) : ℕ := (s.filter (fun v => marked v = true)).card

def allowedCount (n c : ℕ) : Prop :=
  if n = 16 then c=0 ∨ c=2 ∨ c=4 ∨ c=6 ∨ c=12 else c=6 ∨ c=10

instance (n c : ℕ) : Decidable (allowedCount n c) := inferInstanceAs (Decidable (ite _ _ _))

inductive CountTree where
  | impossible : CountTree
  | bounds : CountTree
  | branch : Fin 192 → CountTree → CountTree → CountTree

def boundsCheck (n : ℕ) (l u : Finset (Fin 192)) : Bool :=
  (List.range (n+1)).all fun c => decide
    ((markedCount l ≤ c ∧ c ≤ markedCount u ∧
      l.card-markedCount l ≤ n-c ∧ n-c ≤ u.card-markedCount u) → allowedCount n c)

def countCheck (n : ℕ) : CountTree → Finset (Fin 192) → Finset (Fin 192) → Bool
  | .impossible,l,u => decide (¬ l ⊆ u ∨ n < l.card ∨ u.card < n)
  | .bounds,l,u => boundsCheck n l u
  | .branch v t₀ t₁,l,u =>
      decide (∀w∈l,compatible v w=true) &&
        countCheck n t₀ l (u \ l.image (productVertex v)) &&
        countCheck n t₁ (l ∪ l.image (productVertex v)) (u.filter (fun w => compatible v w = true ∧ productVertex v w ∈ u))

private theorem marked_complement (s : Finset (Fin 192)) :
    (s.filter (fun v => marked v ≠ true)).card = s.card-markedCount s := by
  have hh := Finset.card_filter_add_card_filter_not (s := s) (p := fun v => marked v = true)
  dsimp [markedCount]
  omega

private theorem boundsCheck_sound (n : ℕ) (l u s : Finset (Fin 192))
    (h : boundsCheck n l u = true) (hl : l ⊆ s) (hu : s ⊆ u) (hs : s.card=n) :
    allowedCount n (markedCount s) := by
  have hlA : markedCount l ≤ markedCount s := Finset.card_le_card (Finset.filter_subset_filter _ hl)
  have huA : markedCount s ≤ markedCount u := Finset.card_le_card (Finset.filter_subset_filter _ hu)
  have hlB := Finset.card_le_card (Finset.filter_subset_filter (fun v => marked v ≠ true) hl)
  have huB := Finset.card_le_card (Finset.filter_subset_filter (fun v => marked v ≠ true) hu)
  rw [marked_complement,marked_complement,hs] at hlB
  rw [marked_complement,marked_complement,hs] at huB
  have hc : markedCount s ≤ n := hs ▸ Finset.card_filter_le _ _
  exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_range.mpr (by omega)))
    ⟨hlA,huA,hlB,huB⟩

/-- Soundness uses only actual subgroup multiplication and commutation. -/
theorem countCheck_sound (n : ℕ) (t : CountTree) (l u s : Finset (Fin 192))
    (ht : countCheck n t l u = true) (hl : l ⊆ s) (hu : s ⊆ u) (hs : s.card=n)
    (hcomm : ∀ v ∈ s, ∀ w ∈ s, compatible v w = true)
    (hcoset : ∀ v w, w ∈ s → compatible v w = true →
      (productVertex v w ∈ s ↔ v ∈ s)) : allowedCount n (markedCount s) := by
  induction t generalizing l u with
  | impossible =>
    have hh : ¬ l ⊆ u ∨ n < l.card ∨ u.card < n := of_decide_eq_true ht
    rcases hh with hh | hh | hh
    · exact (hh (hl.trans hu)).elim
    · have hb := Finset.card_le_card hl; omega
    · have hb := Finset.card_le_card hu; omega
  | bounds => exact boundsCheck_sound n l u s ht hl hu hs
  | branch v t₀ t₁ ih₀ ih₁ =>
    have hh : (decide (∀w∈l,compatible v w=true) = true ∧
        countCheck n t₀ l (u \ l.image (productVertex v)) = true) ∧
        countCheck n t₁ (l ∪ l.image (productVertex v))
          (u.filter (fun w => compatible v w = true ∧ productVertex v w ∈ u)) = true := by
      simpa only [countCheck,Bool.and_eq_true] using ht
    have hc (w) (hw : w ∈ l) : compatible v w = true := of_decide_eq_true hh.1.1 w hw
    by_cases hv : v ∈ s
    · apply ih₁ _ _ hh.2
      · intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hl hw
        · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hw
          exact (hcoset v x (hl hx) (hc x hx)).mpr hv
      · intro w hw
        exact Finset.mem_filter.mpr ⟨hu hw,hcomm v hv w hw,hu ((hcoset v w hw (hcomm v hv w hw)).mpr hv)⟩
    · apply ih₀ _ _ hh.1.2 hl
      intro w hw
      refine Finset.mem_sdiff.mpr ⟨hu hw,?_⟩
      rintro hm
      obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hm
      exact hv ((hcoset v x (hl hx) (hc x hx)).mp (he.symm ▸ hw))

end Held.OrdinaryElementary.NativeCoverage
