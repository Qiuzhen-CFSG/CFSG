module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.CosetCover.Words
public import Theory.GroupTheory.CosetWordCertificate.RelatorScan

/-!
# Sound replay of Schreier subgroup-generation deductions

A recorded coset enumeration is translated to equations in the 367 literal
Schreier labels. Representatives here are explicit words in those labels.
Free equalities, the two protected subgroup generators, reversal, composition,
and cancellation along signed cyclic source-relator scans preserve subgroup
membership. Every computational premise is checked separately in the kernel.

Source: the six ATLAS G23G1-P1 relators and G23G1-max3W1 words, as fixed in
`CosetCover.Words`; the producer adapts the project's J₃ M₁ coset replay.
-/

@[expose] public section
open Subgroup.CosetWordCertificate
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate

def sourceRelator (r : Nat) : Word Label :=
  if h : r < 2184 then rawTrace (r / 6) (relatorLetters ⟨r % 6, Nat.mod_lt _ (by decide)⟩)
  else if r = 2184 then rawTrace 0 (boundLetters false) ++ [(protectedLabel false, false)]
  else if r = 2185 then rawTrace 0 (boundLetters true) ++ [(protectedLabel true, false)]
  else []

theorem sourceRelator_eval {G : Type*} [Group G] (x : Label → G)
    (h : RawRelations x) (r : Nat) : eval x (sourceRelator r) = 1 := by
  unfold sourceRelator
  split
  · rename_i hr
    exact h.1 ⟨r / 6, by omega⟩ _
  · split
    · simp only [eval_append, eval_letter, Bool.false_eq_true, ↓reduceIte, h.2]
      exact mul_inv_cancel _
    · split
      · simp only [eval_append, eval_letter, Bool.false_eq_true, ↓reduceIte, h.2]
        exact mul_inv_cancel _
      · exact eval_nil _

def relator (code : Nat) : Word Label :=
  let w := sourceRelator (code / 128)
  let v := if code / 64 % 2 == 0 then w else FreeGroup.invRev w
  v.drop (code % 64) ++ v.take (code % 64)

theorem relator_eval {G : Type*} [Group G] (x : Label → G)
    (h : RawRelations x) (code : Nat) : eval x (relator code) = 1 := by
  let w := sourceRelator (code / 128)
  let v := if code / 64 % 2 == 0 then w else FreeGroup.invRev w
  have hv : eval x v = 1 := by
    dsimp [v]
    split
    · exact sourceRelator_eval x h _
    · rw [eval_invRev, sourceRelator_eval x h, inv_one]
  have ht : eval x (v.take (code % 64)) * eval x (v.drop (code % 64)) = 1 := by
    rw [← eval_append, List.take_append_drop]
    exact hv
  exact (eval_append x _ _).trans (mul_eq_one_comm.mp ht)

inductive Op where
  | free
  | subgroup (b : Bool)
  | reverse (p : Nat)
  | compose (p q : Nat)
  | scan (start relation : Nat) (left right : List Nat)

def check (reps rels : Nat → Word Label) (fs : Nat → FactData Label)
    (n : Nat) (op : Op) : Bool :=
  let f := fs n
  match op with
  | .free => decide (reduce (reps f.left ++ f.word) = reps f.right)
  | .subgroup b => decide (f = ⟨0, [(protectedLabel b, true)], 0⟩)
  | .reverse p => decide (p < n) && decide
      (f = ⟨(fs p).right, FreeGroup.invRev (fs p).word, (fs p).left⟩)
  | .compose p q => decide (p < n ∧ q < n ∧ (fs p).right = (fs q).left) &&
      decide (f = ⟨(fs p).left, reduce ((fs p).word ++ (fs q).word), (fs q).right⟩)
  | .scan i r ps qs =>
      Scan.pathCheck fs n i ps f.left && Scan.pathCheck fs n i qs f.right &&
      decide (f.word = reduce (FreeGroup.invRev (Scan.pathWord fs ps) ++
        rels r ++ Scan.pathWord fs qs))

private theorem holds_append {G : Type*} [Group G]
    {H : Subgroup G} {x : Label → G} {ρ : Nat → G}
    {f k : FactData Label} (hf : Holds H x ρ f) (hk : Holds H x ρ k)
    (hm : f.right = k.left) :
    Holds H x ρ ⟨f.left, f.word ++ k.word, k.right⟩ := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hk
  refine ⟨a*b, ?_⟩
  change ρ f.left * eval x (f.word ++ k.word) = (a.val*b.val) * ρ k.right
  rw [eval_append, ← mul_assoc, ha, mul_assoc, hm, hb, ← mul_assoc]

theorem check_sound {G : Type*} [Group G] (x : Label → G)
    (reps rels : Nat → Word Label) (h : ∀ r, eval x (rels r) = 1) (hroot : reps 0 = []) (fs : Nat → FactData Label)
    (n : Nat) (op : Op)
    (prior : ∀ p, p < n → Holds (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (reps i)) (fs p))
    (hc : check reps rels fs n op = true) :
    Holds (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (reps i)) (fs n) := by
  cases op with
  | free =>
    have he : reduce (reps (fs n).left ++ (fs n).word) = reps (fs n).right := by
      simpa [check] using hc
    refine ⟨1, ?_⟩
    change eval x (reps (fs n).left) * eval x (fs n).word = 1 * eval x (reps (fs n).right)
    rw [one_mul, ← eval_append, ← eval_reduce, he]
  | subgroup b =>
    have he : fs n = ⟨0, [(protectedLabel b, true)], 0⟩ := by simpa [check] using hc
    rw [he]
    apply holds_subgroup (by simp [hroot])
    simpa using (Subgroup.subset_closure (k := Set.range fun b => x (protectedLabel b)) ⟨b, rfl⟩)
  | reverse p =>
    have he : p < n ∧ fs n = ⟨(fs p).right, FreeGroup.invRev (fs p).word, (fs p).left⟩ := by
      simpa [check] using hc
    rw [he.2]
    exact holds_reverse (prior p he.1)
  | compose p q =>
    have he : (p < n ∧ q < n ∧ (fs p).right = (fs q).left) ∧
        fs n = ⟨(fs p).left, reduce ((fs p).word ++ (fs q).word), (fs q).right⟩ := by
      simpa [check] using hc
    rw [he.2]
    exact holds_compose he.1.2.2 (prior p he.1.1) (prior q he.1.2.1)
  | scan i r ps qs =>
    have he : Scan.pathCheck fs n i ps (fs n).left = true ∧
        Scan.pathCheck fs n i qs (fs n).right = true ∧
        (fs n).word = reduce (FreeGroup.invRev (Scan.pathWord fs ps) ++
          rels r ++ Scan.pathWord fs qs) := by
      simpa [check, and_assoc] using hc
    have hp := Scan.pathCheck_sound fs n prior ps i (fs n).left he.1
    have hq := Scan.pathCheck_sound fs n prior qs i (fs n).right he.2.1
    have hr := holds_relator (H := Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      (ρ := fun i => eval x (reps i)) i _ (h r)
    have hall := holds_append (holds_append (holds_reverse hp) hr rfl) hq rfl
    have hrw : eval x (FreeGroup.invRev (Scan.pathWord fs ps) ++
        rels r ++ Scan.pathWord fs qs) = eval x (fs n).word := by
      rw [he.2.2, eval_reduce]
    simp only [List.append_assoc] at hrw
    simpa only [Holds, List.append_assoc, hrw] using hall

def checkChunk (reps rels : Nat → Word Label) (fs : Nat → FactData Label)
    (ops : Nat → Op) (start count : Nat) : Bool :=
  (List.range count).all fun k => check reps rels fs (start + k) (ops (start + k))

theorem chunk_sound {G : Type*} [Group G] (x : Label → G)
    (reps rels : Nat → Word Label) (hr : ∀ r, eval x (rels r) = 1)
    (hroot : reps 0 = []) (fs : Nat → FactData Label) (ops : Nat → Op)
    (start count : Nat)
    (prior : ∀ n, n < start → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (reps i)) (fs n))
    (hc : checkChunk reps rels fs ops start count = true) :
    ∀ n, n < start + count → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (reps i)) (fs n) := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hlo : n < start
    · exact prior n hlo
    have hm : n - start ∈ List.range count := by simp only [List.mem_range]; omega
    have hc' := List.all_eq_true.mp hc (n - start) hm
    have he : start + (n - start) = n := by omega
    rw [he] at hc'
    exact check_sound x reps rels hr hroot fs n (ops n)
      (fun p hp => ih p hp (by omega)) hc'

/-- Output paths at the empty representative prove literal generator membership. -/
theorem output_mem {G : Type*} [Group G] (x : Label → G)
    (reps : Nat → Word Label) (hroot : reps 0 = [])
    (fs : Nat → FactData Label) (N : Nat)
    (hs : ∀ n, n < N → Holds
      (Subgroup.closure (Set.range fun b => x (protectedLabel b)))
      x (fun i => eval x (reps i)) (fs n))
    (k : Label) (ps : List Nat)
    (hp : Scan.pathCheck fs N 0 ps 0 = true)
    (hw : reduce (Scan.pathWord fs ps) = [(k, true)]) :
    x k ∈ Subgroup.closure (Set.range fun b => x (protectedLabel b)) := by
  obtain ⟨a, ha⟩ := Scan.pathCheck_sound fs N hs ps 0 0 hp
  have he : eval x (Scan.pathWord fs ps) = x k := by
    rw [← eval_reduce, hw, eval_letter]
    rfl
  simp only [hroot, eval_nil, he, one_mul, mul_one] at ha
  exact ha.symm ▸ a.property

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.SchreierCover.GenerationCertificate
