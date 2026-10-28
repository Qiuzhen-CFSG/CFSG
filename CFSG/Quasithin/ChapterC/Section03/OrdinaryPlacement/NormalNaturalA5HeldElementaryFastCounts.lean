module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryFastProductTable
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryCountChecker

/-!
# A short interval test for the native Held count certificates

The possible counts lie between two computable bounds. The allowed values
are isolated, so a singleton allowed interval suffices. This avoids checking
the same set cardinalities once for every possible count at every leaf.
-/
@[expose] public section
namespace Held.OrdinaryElementary.NativeCoverage

def fastMarked (v : Fin 192) : Bool := (735598034995998750088795186131567928462650018381260914686:ℕ).testBit v.val

private theorem fastMarked_eq : ∀v,fastMarked v=marked v := by
  decide +kernel

def fastMarkedCount (s : Finset (Fin 192)) : ℕ := (s.filter (fun v=>fastMarked v=true)).card

private theorem fastMarkedCount_eq (s : Finset (Fin 192)) : fastMarkedCount s=markedCount s := by
  simp only [fastMarkedCount,markedCount,fastMarked_eq]

def fastBoundsCheck (n : ℕ) (l u : Finset (Fin 192)) : Bool :=
  let lo := max (fastMarkedCount l) (n-(u.card-fastMarkedCount u))
  let hi := min (fastMarkedCount u) (n-(l.card-fastMarkedCount l))
  decide (hi<lo ∨ lo=hi ∧ allowedCount n lo)

private theorem fastBoundsCheck_sound (n : ℕ) (l u s : Finset (Fin 192))
    (h : fastBoundsCheck n l u=true) (hl : l⊆s) (hu : s⊆u) (hs : s.card=n) :
    allowedCount n (markedCount s) := by
  have h : decide (min (markedCount u) (n-(l.card-markedCount l))<
      max (markedCount l) (n-(u.card-markedCount u)) ∨
      max (markedCount l) (n-(u.card-markedCount u))=
        min (markedCount u) (n-(l.card-markedCount l)) ∧
      allowedCount n (max (markedCount l) (n-(u.card-markedCount u))))=true := by
    simpa only [fastBoundsCheck,fastMarkedCount_eq] using h
  have hlA : markedCount l ≤ markedCount s := Finset.card_le_card (Finset.filter_subset_filter _ hl)
  have huA : markedCount s ≤ markedCount u := Finset.card_le_card (Finset.filter_subset_filter _ hu)
  have hc : markedCount s ≤ n := hs ▸ Finset.card_filter_le _ _
  have hlB := Finset.card_le_card (Finset.filter_subset_filter (fun v => marked v ≠ true) hl)
  have huB := Finset.card_le_card (Finset.filter_subset_filter (fun v => marked v ≠ true) hu)
  have hcomp (s : Finset (Fin 192)) :
      (s.filter (fun v => marked v ≠ true)).card=s.card-markedCount s := by
    have hh := Finset.card_filter_add_card_filter_not (s:=s) (p:=fun v=>marked v=true)
    dsimp [markedCount]
    omega
  rw [hcomp,hcomp,hs] at hlB
  rw [hcomp,hcomp,hs] at huB
  have hlo : max (markedCount l) (n-(u.card-markedCount u))≤markedCount s := by omega
  have hhi : markedCount s≤min (markedCount u) (n-(l.card-markedCount l)) := by omega
  have hh : min (markedCount u) (n-(l.card-markedCount l))<
      max (markedCount l) (n-(u.card-markedCount u)) ∨
      max (markedCount l) (n-(u.card-markedCount u))=
        min (markedCount u) (n-(l.card-markedCount l)) ∧
      allowedCount n (max (markedCount l) (n-(u.card-markedCount u))) := of_decide_eq_true h
  rcases hh with hh | ⟨he,ha⟩
  · omega
  · have heq : max (markedCount l) (n-(u.card-markedCount u))=markedCount s := by omega
    rwa [heq] at ha

def fastCountCheck (n : ℕ) : CountTree → Finset (Fin 192) → Finset (Fin 192) → Bool
  | .impossible,l,u => decide (¬ l ⊆ u ∨ n < l.card ∨ u.card < n)
  | .bounds,l,u => fastBoundsCheck n l u
  | .branch v t₀ t₁,l,u =>
      decide (∀w∈l,compatible v w=true) &&
        fastCountCheck n t₀ l (u \ l.image (fastProductVertex v)) &&
        fastCountCheck n t₁ (l ∪ l.image (fastProductVertex v)) (u.filter (fun w => compatible v w = true ∧ fastProductVertex v w ∈ u))

/-- Soundness uses only actual subgroup multiplication and commutation. -/
theorem fastCountCheck_sound (n : ℕ) (t : CountTree) (l u s : Finset (Fin 192))
    (ht : fastCountCheck n t l u = true) (hl : l ⊆ s) (hu : s ⊆ u) (hs : s.card=n)
    (hcomm : ∀ v ∈ s, ∀ w ∈ s, compatible v w = true)
    (hcoset : ∀ v w, w ∈ s → compatible v w = true →
      (productVertex v w ∈ s ↔ v ∈ s)) : allowedCount n (markedCount s) := by
  have hcoset : ∀v w,w∈s → compatible v w=true →
      (fastProductVertex v w∈s ↔ v∈s) := by
    simpa only [fastProductVertex_eq] using hcoset
  induction t generalizing l u with
  | impossible =>
    have hh : ¬ l ⊆ u ∨ n < l.card ∨ u.card < n := of_decide_eq_true ht
    rcases hh with hh | hh | hh
    · exact (hh (hl.trans hu)).elim
    · have hb := Finset.card_le_card hl; omega
    · have hb := Finset.card_le_card hu; omega
  | bounds => exact fastBoundsCheck_sound n l u s ht hl hu hs
  | branch v t₀ t₁ ih₀ ih₁ =>
    have hh : (decide (∀w∈l,compatible v w=true) = true ∧
        fastCountCheck n t₀ l (u \ l.image (fastProductVertex v)) = true) ∧
        fastCountCheck n t₁ (l ∪ l.image (fastProductVertex v))
          (u.filter (fun w => compatible v w = true ∧ fastProductVertex v w ∈ u)) = true := by
      simpa only [fastCountCheck,Bool.and_eq_true] using ht
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
