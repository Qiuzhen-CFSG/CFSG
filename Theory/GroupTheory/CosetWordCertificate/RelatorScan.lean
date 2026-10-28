module

public import Theory.GroupTheory.CosetWordCertificateBoolean

/-!
# Compact relator scans for coset-word certificates

Each scan cancels already justified forward and backward paths from an actual
relator loop. The resulting equation has a witness in the subgroup. This is
the same deduction as reversal and composition in `CosetWordCertificate`,
without storing each intermediate path as a separate proof node.

Source: the Todd–Coxeter method. Adapted from the checked J₃ M₁ scan
checker in `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Cover/Scan.lean`.
The compact Sp₆(2) subgroup presentation supplies an independent consumer.
-/

@[expose] public section

open Subgroup.CosetWordCertificate
namespace Subgroup.CosetWordCertificate.Scan
variable {G α : Type*} [Group G]

/-- The signed word read by a list of already justified edges. -/
def pathWord (fs : Nat → FactData α) : List Nat → Word α
  | [] => []
  | p :: ps => (fs p).word ++ pathWord fs ps

/-- Every edge must be earlier, and endpoints must join literally. -/
def pathCheck (fs : Nat → FactData α) (n : Nat) : Nat → List Nat → Nat → Bool
  | i, [], j => i == j
  | i, p :: ps, j => Nat.blt p n && (i == (fs p).left) &&
      pathCheck fs n (fs p).right ps j

private theorem holds_append {H : Subgroup G} {g : α → G} {ρ : Nat → G}
    {f k : FactData α} (hf : Holds H g ρ f) (hk : Holds H g ρ k)
    (hm : f.right = k.left) :
    Holds H g ρ ⟨f.left, f.word ++ k.word, k.right⟩ := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hk
  refine ⟨a*b, ?_⟩
  change ρ f.left * eval g (f.word ++ k.word) = (a.val*b.val) * ρ k.right
  rw [eval_append, ← mul_assoc, ha, mul_assoc, hm, hb, ← mul_assoc]

theorem pathCheck_sound {H : Subgroup G} {g : α → G} {ρ : Nat → G}
    (fs : Nat → FactData α) (n : Nat)
    (prior : ∀ p, p < n → Holds H g ρ (fs p)) (ps : List Nat) (i j : Nat)
    (h : pathCheck fs n i ps j = true) :
    Holds H g ρ ⟨i, pathWord fs ps, j⟩ := by
  induction ps generalizing i with
  | nil =>
    have hij : i = j := by simpa [pathCheck] using h
    subst j
    exact holds_refl i
  | cons p ps ih =>
    have h' : p < n ∧ i = (fs p).left ∧ pathCheck fs n (fs p).right ps j = true := by
      simpa [pathCheck, and_assoc] using h
    rw [h'.2.1]
    exact holds_append (prior p h'.1) (ih _ h'.2.2) rfl

inductive Op (α : Type*) where
  | basic (op : Instruction α)
  | scan (start relator : Nat) (left right : List Nat)

/-- A scan cancels the known forward and backward paths from a relator loop. -/
def check [BEq α] [DecidableEq α] (C : Context α) (fs : Nat → FactData α)
    (n : Nat) (op : Op α) : Bool :=
  match op with
  | .basic op => checkBool C fs n op (fs n)
  | .scan i r ps qs =>
      pathCheck fs n i ps (fs n).left && pathCheck fs n i qs (fs n).right &&
      ((fs n).word == reduce (FreeGroup.invRev (pathWord fs ps) ++
        C.relator r ++ pathWord fs qs))

private theorem holds_reduce [DecidableEq α]
    {H : Subgroup G} {g : α → G} {ρ : Nat → G} {f : FactData α}
    (h : Holds H g ρ f) : Holds H g ρ ⟨f.left, reduce f.word, f.right⟩ := by
  simpa only [Holds, eval_reduce] using h

theorem check_sound [BEq α] [LawfulBEq α] [DecidableEq α]
    {C : Context α} {H : Subgroup G} {g : α → G} {ρ : Nat → G}
    (valid : Valid C H g ρ) (fs : Nat → FactData α) (n : Nat) (op : Op α)
    (prior : ∀ p, p < n → Holds H g ρ (fs p))
    (h : check C fs n op = true) : Holds H g ρ (fs n) := by
  cases op with
  | basic op =>
    exact Subgroup.CosetWordCertificate.check_sound valid fs n op (fs n)
      ((checkBool_iff C fs n op (fs n)).mp h) (fun p hp _ => prior p hp)
  | scan i r ps qs =>
    have h' : pathCheck fs n i ps (fs n).left = true ∧
        pathCheck fs n i qs (fs n).right = true ∧
        (fs n).word = reduce (FreeGroup.invRev (pathWord fs ps) ++
          C.relator r ++ pathWord fs qs) := by
      simpa [check, and_assoc] using h
    have hp := pathCheck_sound fs n prior ps i (fs n).left h'.1
    have hq := pathCheck_sound fs n prior qs i (fs n).right h'.2.1
    have hr : Holds H g ρ ⟨i, C.relator r, i⟩ := holds_relator i _ (valid.relator r)
    have hpre := holds_append (holds_reverse hp) hr rfl
    have hall := holds_reduce (holds_append hpre hq rfl)
    have hw := h'.2.2
    simp only [List.append_assoc] at hall hw
    rw [← hw] at hall
    exact hall

def checkChunk [BEq α] [DecidableEq α] (C : Context α)
    (fs : Nat → FactData α) (ops : Nat → Op α) (start count : Nat) : Bool :=
  (List.range count).all fun k => check C fs (start+k) (ops (start+k))

theorem chunk_sound [BEq α] [LawfulBEq α] [DecidableEq α]
    {C : Context α} {H : Subgroup G} {g : α → G} {ρ : Nat → G}
    (valid : Valid C H g ρ) (fs : Nat → FactData α) (ops : Nat → Op α)
    (start count : Nat) (prior : ∀ n, n < start → Holds H g ρ (fs n))
    (checked : checkChunk C fs ops start count = true) :
    ∀ n, n < start+count → Holds H g ρ (fs n) := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hlo : n < start
    · exact prior n hlo
    have hm : n-start ∈ List.range count := by simp only [List.mem_range]; omega
    have hc := List.all_eq_true.mp checked (n-start) hm
    have he : start + (n-start) = n := by omega
    rw [he] at hc
    exact check_sound valid fs n (ops n) (fun p hp => ih p hp (by omega)) hc
end Subgroup.CosetWordCertificate.Scan
