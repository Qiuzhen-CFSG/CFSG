module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryData

/-!
# Sound branching certificates for large cliques

A branch asks whether a vertex lies in the clique. The negative branch deletes
it; the positive branch keeps only its commuting vertices. A leaf either has
fewer than 16 possible vertices or lies in one of the six candidate masks.
The induction below proves the checker sound for every finite clique.
-/
@[expose] public section
namespace Held.OrdinaryElementary.NativeCoverage

inductive Tree where
  | small : Tree
  | covered : Fin 34 → Tree
  | branch : Fin 192 → Tree → Tree → Tree

def check : Tree → List (Fin 192) → Bool
  | .small, u => decide (u.length < 16)
  | .covered k, u => u.all (fun v => (candidateMask k).testBit v.val)
  | .branch v l r, u =>
      check l (u.filter (fun w => w != v)) &&
      check r (u.filter (compatible v))

theorem check_sound (t : Tree) (u : List (Fin 192)) (ht : check t u = true)
    (s : Finset (Fin 192)) (hs : ∀ v ∈ s, v ∈ u) (hcard : 16 ≤ s.card)
    (hc : ∀ v ∈ s, ∀ w ∈ s, compatible v w = true) :
    ∃ k : Fin 34, ∀ v ∈ s, (candidateMask k).testBit v.val = true := by
  induction t generalizing u with
  | small =>
    have hlt : u.length < 16 := of_decide_eq_true ht
    have hle : s.card ≤ u.length :=
      (Finset.card_le_card (fun v hv => List.mem_toFinset.mpr (hs v hv))).trans
        (List.toFinset_card_le u)
    omega
  | covered k =>
    exact ⟨k, fun v hv => List.all_eq_true.mp ht v (hs v hv)⟩
  | branch v l r ihl ihr =>
    have ⟨hl, hr⟩ : check l (u.filter (fun w => w != v)) = true ∧
        check r (u.filter (compatible v)) = true := by
      simpa only [check, Bool.and_eq_true] using ht
    by_cases hv : v ∈ s
    · apply ihr _ hr
      intro w hw
      exact List.mem_filter.mpr ⟨hs w hw, hc v hv w hw⟩
    · apply ihl _ hl
      intro w hw
      apply List.mem_filter.mpr
      exact ⟨hs w hw, by simpa only [bne_iff_ne] using (show w ≠ v by rintro rfl; exact hv hw)⟩

end Held.OrdinaryElementary.NativeCoverage
