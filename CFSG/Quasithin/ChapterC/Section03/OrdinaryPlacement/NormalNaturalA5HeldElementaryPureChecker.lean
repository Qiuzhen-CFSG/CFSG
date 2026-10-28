module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryCountChecker

/-!
# Pure elementary subgroup coverage inside the native Held Sylow

The finite checker propagates genuine multiplication cosets. Its terminal
sets are the six maximal pure order-sixteen rows and the two order-sixty-four
cores. This is a checked coverage statement, not an enumeration hypothesis.
-/

@[expose] public section
namespace Held.OrdinaryElementary.NativeCoverage

def pureTarget : Fin 8 → Fin 34
  | 0 => 13 | 1 => 14 | 2 => 24 | 3 => 25
  | 4 => 26 | 5 => 27 | 6 => 32 | 7 => 33

def pureTargetSet (k : Fin 8) : Finset (Fin 192) :=
  Finset.univ.filter (fun v => (candidateMask (pureTarget k)).testBit v.val = true)

inductive PureTree where
  | impossible : PureTree
  | covered : Fin 8 → PureTree
  | branch : Fin 192 → PureTree → PureTree → PureTree

def pureCheck : PureTree → Finset (Fin 192) → Finset (Fin 192) → Bool
  | .impossible,l,u => decide (¬ l ⊆ u ∨ 16 < l.card ∨ u.card < 16)
  | .covered k,_,u => decide (u ⊆ pureTargetSet k)
  | .branch v t₀ t₁,l,u =>
      decide (∀w∈l,compatible v w=true) &&
        pureCheck t₀ l (u \ l.image (productVertex v)) &&
        pureCheck t₁ (l ∪ l.image (productVertex v))
          (u.filter (fun w => compatible v w=true ∧ productVertex v w∈u))

/-- Soundness uses only actual subgroup multiplication and commutation. -/
theorem pureCheck_sound (t : PureTree) (l u s : Finset (Fin 192))
    (ht : pureCheck t l u = true) (hl : l ⊆ s) (hu : s ⊆ u) (hs : s.card=16)
    (hcomm : ∀ v ∈ s, ∀ w ∈ s, compatible v w = true)
    (hcoset : ∀ v w, w ∈ s → compatible v w = true →
      (productVertex v w ∈ s ↔ v ∈ s)) : ∃k : Fin 8, s ⊆ pureTargetSet k := by
  induction t generalizing l u with
  | impossible =>
    have hh : ¬ l ⊆ u ∨ 16 < l.card ∨ u.card < 16 := of_decide_eq_true ht
    rcases hh with hh | hh | hh
    · exact (hh (hl.trans hu)).elim
    · have hb := Finset.card_le_card hl; omega
    · have hb := Finset.card_le_card hu; omega
  | covered k => exact ⟨k,hu.trans (of_decide_eq_true ht)⟩
  | branch v t₀ t₁ ih₀ ih₁ =>
    have hh : (decide (∀w∈l,compatible v w=true) = true ∧
        pureCheck t₀ l (u \ l.image (productVertex v)) = true) ∧
        pureCheck t₁ (l ∪ l.image (productVertex v))
          (u.filter (fun w => compatible v w = true ∧ productVertex v w ∈ u)) = true := by
      simpa only [pureCheck,Bool.and_eq_true] using ht
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
