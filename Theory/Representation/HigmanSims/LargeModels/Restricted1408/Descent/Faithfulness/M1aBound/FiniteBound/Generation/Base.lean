module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.Presentation
public import Theory.GroupTheory.CosetWordCertificate.RelatorScan

/-! Checked generation of the exact HS Schreier presentation by its first three
generators. Source: the literal 1,300 Schreier relators; see source/README.md.
The untrusted trace supplies only six-rule deductions and relator scans. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier
open Subgroup.CosetWordCertificate

/-- The literal first three Schreier generators, with zero-based indices. -/
def threeGenerator (i : Fin 3) : Carrier := localGenerator ⟨i.val, by omega⟩

def threeSubgroup : Subgroup Carrier := Subgroup.closure (Set.range threeGenerator)

namespace GenerationCertificate

def branch {α : Type*} (cutoff : Nat) (left right : Nat → α) (i : Nat) : α :=
  if i < cutoff then left i else right i

def unpack (pages : Nat → Nat) (bits i : Nat) : Nat :=
  (pages (i / 128) >>> (bits * (i % 128))) % (2 ^ bits)

def decode (a : Nat) : Letter (Fin 101) :=
  (⟨(a / 2) % 101, Nat.mod_lt _ (by decide)⟩, a % 2 == 0)

def allowed (a : Letter (Fin 101)) : Bool := a.1.val < 3

theorem allowed_mem (a : Letter (Fin 101)) (ha : allowed a = true) :
    eval localGenerator [a] ∈ threeSubgroup := by
  have hi : a.1.val < 3 := by simpa only [allowed, decide_eq_true_eq] using ha
  have hg : localGenerator a.1 ∈ threeSubgroup :=
    Subgroup.subset_closure ⟨⟨a.1.val, hi⟩, rfl⟩
  rw [eval_letter]
  split
  · exact hg
  · exact threeSubgroup.inv_mem hg

/-- Balance the conjunction so certificate size does not increase recursion depth. -/
def allBlock (p : Nat → Bool) : Nat → Nat → Bool
  | 0, start => p start
  | depth + 1, start => allBlock p depth start && allBlock p depth (start + 2 ^ depth)

theorem allBlock_spec (p : Nat → Bool) (depth start : Nat)
    (h : allBlock p depth start = true) :
    ∀ n, start ≤ n → n < start + 2 ^ depth → p n = true := by
  induction depth generalizing start with
  | zero =>
    intro n hlo hhi
    have hn : n = start := by omega
    subst n
    exact h
  | succ depth ih =>
    simp only [allBlock, Bool.and_eq_true] at h
    intro n hlo hhi
    rw [Nat.pow_succ, Nat.mul_two] at hhi
    by_cases hn : n < start + 2 ^ depth
    · exact ih start h.1 n hlo hn
    · exact ih (start + 2 ^ depth) h.2 n (by omega) (by omega)

end GenerationCertificate

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier
