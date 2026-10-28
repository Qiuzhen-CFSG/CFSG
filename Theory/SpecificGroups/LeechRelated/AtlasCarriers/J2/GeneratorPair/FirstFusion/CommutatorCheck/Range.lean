module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.CommutatorCheck.Data

/-!
# Sound bounded Boolean checks

A check on each of sixty blocks of size 32 covers all 1920 published
centralizer-word indices. These helpers connect the finite certificates to
ordinary universal quantification, without evaluating permutation words.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.CommutatorCheck

theorem checkFin_iff {n : Nat} (f : Fin n → Bool) :
    checkFin f = true ↔ ∀ i, f i = true := by
  constructor
  · intro h i
    have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
    simpa only [dif_pos i.isLt] using hi
  · intro h
    apply List.all_eq_true.mpr
    intro i hi
    have hn := List.mem_range.mp hi
    rw [dif_pos hn]
    exact h ⟨i, hn⟩

def checkRange {n : Nat} (f : Fin n → Bool) (lo count : Nat) : Bool :=
  (List.range count).all fun k => if h : lo + k < n then f ⟨lo + k, h⟩ else true

theorem checkRange_sound {n : Nat} (f : Fin n → Bool) (lo count : Nat)
    (h : checkRange f lo count = true) (i : Fin n)
    (hlo : lo ≤ i.val) (hhi : i.val < lo + count) : f i = true := by
  have hk : i.val - lo < count := by omega
  have he : lo + (i.val - lo) = i.val := by omega
  have hi := List.all_eq_true.mp h (i.val - lo) (List.mem_range.mpr hk)
  simpa only [he, dif_pos i.isLt] using hi

theorem all_of_blocks (f : Fin 1920 → Bool)
    (h : ∀ k : Fin 60, checkRange f (k.val * 32) 32 = true) (i : Fin 1920) :
    f i = true := by
  have hk : i.val / 32 < 60 := by omega
  have hh : checkRange f ((i.val / 32) * 32) 32 = true := h ⟨i.val / 32, hk⟩
  exact checkRange_sound f _ _ hh i (by omega) (by omega)

end Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.CommutatorCheck
