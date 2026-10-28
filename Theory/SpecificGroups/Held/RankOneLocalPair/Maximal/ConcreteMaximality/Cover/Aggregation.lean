module

public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.ConcreteMaximality.Cover.Computation

/-!
# Combining independent cover checks

A recursive conjunction combines the checked rows without re-evaluating their
permutation computations. The extraction lemma selects any array entry with
its original index. This is logical proof assembly, independent of Held.
-/

@[expose] public section
namespace Held.RankOneLocalPair.ConcreteMaximality.CoverCertificate

def AllRows : List Row → Prop
  | [] => True
  | r :: rs => rowCheck r = true ∧ AllRows rs

theorem AllRows.get {rs : List Row} (h : AllRows rs) (i : Fin rs.length) :
    rowCheck (rs[i.val]!) = true := by
  induction rs with
  | nil => exact Fin.elim0 i
  | cons r rs ih =>
    rcases h with ⟨hr,hs⟩
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hr
    · exact ih hs k

theorem checked_of_allRows (rs : Array Row) (h : AllRows rs.toList)
    (i : Fin rs.size) : rowCheck (rs[i.val]!) = true := by
  simpa only [Array.length_toList, Array.getElem!_toList] using
    h.get ⟨i.val, by simpa only [Array.length_toList] using i.isLt⟩

def AllAt (P : ℕ → Row → Prop) : ℕ → List Row → Prop
  | _, [] => True
  | n, r :: rs => P n r ∧ AllAt P (n+1) rs

theorem AllAt.get {P : ℕ → Row → Prop} {rs : List Row} {start : ℕ}
    (h : AllAt P start rs) (i : Fin rs.length) : P (start+i.val) (rs[i.val]!) := by
  induction rs generalizing start with
  | nil => exact Fin.elim0 i
  | cons r rs ih =>
    rcases h with ⟨hr,hs⟩
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hr
    · simpa only [Fin.val_succ, Nat.add_right_comm, Nat.add_assoc, List.getElem!_cons_succ] using ih hs k

theorem aligned_of_allAt (P : ℕ → Row → Prop) (start : ℕ) (rs : Array Row)
    (h : AllAt P start rs.toList) (i : Fin rs.size) : P (start+i.val) (rs[i.val]!) := by
  simpa only [Array.length_toList, Array.getElem!_toList] using
    h.get ⟨i.val, by simpa only [Array.length_toList] using i.isLt⟩

end Held.RankOneLocalPair.ConcreteMaximality.CoverCertificate
