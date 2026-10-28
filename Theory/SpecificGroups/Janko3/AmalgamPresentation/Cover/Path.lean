module

public import Theory.GroupTheory.CosetWordCertificate.RelatorScan

/-!
# Compressed paths in the universal amalgam coset certificate

Defining edges and subgroup loops are valid directly from the context. Signed
references avoid storing reversals, and paths compose already established
facts. Every checked instruction still asserts an actual subgroup witness.
-/

@[expose] public section
namespace Sporadic.Janko3.AmalgamPresentation.Cover.Path
open Subgroup.CosetWordCertificate
variable {G α : Type*} [Group G]

def baseData (C : Context α) (decode : Nat → Letter α)
    (fs : Nat → FactData α) (r : Nat) : FactData α :=
  let i := r / 8
  match r % 4 with
  | 0 => fs i
  | 1 => ⟨C.parent i, [C.letter i], i⟩
  | 2 => ⟨0, [decode i], 0⟩
  | _ => ⟨i, [], i⟩

def refData (C : Context α) (decode : Nat → Letter α)
    (fs : Nat → FactData α) (r : Nat) : FactData α :=
  let f := baseData C decode fs r
  if r / 4 % 2 == 0 then f else ⟨f.right, FreeGroup.invRev f.word, f.left⟩

def refCheck (C : Context α) (decode : Nat → Letter α) (n r : Nat) : Bool :=
  match r % 4 with
  | 0 => r / 8 < n
  | 1 => r / 8 != 0
  | 2 => C.allowed (decode (r / 8))
  | _ => true

theorem refCheck_sound {C : Context α} {H : Subgroup G} {g : α → G} {ρ : Nat → G}
    (valid : Valid C H g ρ) (decode : Nat → Letter α) (fs : Nat → FactData α)
    (n r : Nat) (prior : ∀ p, p < n → Holds H g ρ (fs p))
    (h : refCheck C decode n r = true) : Holds H g ρ (refData C decode fs r) := by
  have hb : Holds H g ρ (baseData C decode fs r) := by
    unfold baseData
    unfold refCheck at h
    split <;> rename_i he
    all_goals simp only [he] at h
    · exact prior _ (by simpa using h)
    · exact holds_defining _ _ _ (valid.edge _ (by simpa using h))
    · exact holds_subgroup valid.root _ (valid.subgroup _ h)
    · exact holds_refl _
  unfold refData
  split
  · exact hb
  · exact holds_reverse hb

def pathWord (C : Context α) (decode : Nat → Letter α)
    (fs : Nat → FactData α) : List Nat → Word α
  | [] => []
  | r :: rs => (refData C decode fs r).word ++ pathWord C decode fs rs

def pathCheck (C : Context α) (decode : Nat → Letter α)
    (fs : Nat → FactData α) (n : Nat) : Nat → List Nat → Nat → Bool
  | i, [], j => i == j
  | i, r :: rs, j => refCheck C decode n r && (i == (refData C decode fs r).left) &&
      pathCheck C decode fs n (refData C decode fs r).right rs j

private theorem holds_append {H : Subgroup G} {g : α → G} {ρ : Nat → G}
    {f k : FactData α} (hf : Holds H g ρ f) (hk : Holds H g ρ k)
    (hm : f.right = k.left) :
    Holds H g ρ ⟨f.left, f.word ++ k.word, k.right⟩ := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hk
  refine ⟨a*b, ?_⟩
  change ρ f.left * eval g (f.word ++ k.word) = (a.val*b.val) * ρ k.right
  rw [eval_append, ← mul_assoc, ha, mul_assoc, hm, hb, ← mul_assoc]

theorem pathCheck_sound {C : Context α} {H : Subgroup G} {g : α → G} {ρ : Nat → G}
    (valid : Valid C H g ρ) (decode : Nat → Letter α) (fs : Nat → FactData α)
    (n : Nat) (prior : ∀ p, p < n → Holds H g ρ (fs p))
    (rs : List Nat) (i j : Nat) (h : pathCheck C decode fs n i rs j = true) :
    Holds H g ρ ⟨i, pathWord C decode fs rs, j⟩ := by
  induction rs generalizing i with
  | nil =>
    have hij : i = j := by simpa [pathCheck] using h
    subst j
    exact holds_refl i
  | cons r rs ih =>
    have h' : refCheck C decode n r = true ∧ i = (refData C decode fs r).left ∧
        pathCheck C decode fs n (refData C decode fs r).right rs j = true := by
      simpa [pathCheck, and_assoc] using h
    rw [h'.2.1]
    exact holds_append (refCheck_sound valid decode fs n r prior h'.1) (ih _ h'.2.2) rfl

inductive Op where
  | path (refs : List Nat)
  | scan (start relator : Nat) (left right : List Nat)

def check [BEq α] [DecidableEq α] (C : Context α) (decode : Nat → Letter α)
    (fs : Nat → FactData α) (n : Nat) (op : Op) : Bool :=
  match op with
  | .path rs => pathCheck C decode fs n (fs n).left rs (fs n).right &&
      ((fs n).word == reduce (pathWord C decode fs rs))
  | .scan i r ps qs =>
      pathCheck C decode fs n i ps (fs n).left &&
      pathCheck C decode fs n i qs (fs n).right &&
      ((fs n).word == reduce (FreeGroup.invRev (pathWord C decode fs ps) ++
        C.relator r ++ pathWord C decode fs qs))

private theorem holds_reduce [DecidableEq α]
    {H : Subgroup G} {g : α → G} {ρ : Nat → G} {f : FactData α}
    (h : Holds H g ρ f) : Holds H g ρ ⟨f.left, reduce f.word, f.right⟩ := by
  simpa only [Holds, eval_reduce] using h

theorem check_sound [BEq α] [LawfulBEq α] [DecidableEq α]
    {C : Context α} {H : Subgroup G} {g : α → G} {ρ : Nat → G}
    (valid : Valid C H g ρ) (decode : Nat → Letter α) (fs : Nat → FactData α)
    (n : Nat) (op : Op) (prior : ∀ p, p < n → Holds H g ρ (fs p))
    (h : check C decode fs n op = true) : Holds H g ρ (fs n) := by
  cases op with
  | path rs =>
    have h' : pathCheck C decode fs n (fs n).left rs (fs n).right = true ∧
        (fs n).word = reduce (pathWord C decode fs rs) := by simpa [check] using h
    have hp := holds_reduce (pathCheck_sound valid decode fs n prior rs _ _ h'.1)
    rw [← h'.2] at hp
    exact hp
  | scan i r ps qs =>
    have h' : pathCheck C decode fs n i ps (fs n).left = true ∧
        pathCheck C decode fs n i qs (fs n).right = true ∧
        (fs n).word = reduce (FreeGroup.invRev (pathWord C decode fs ps) ++
          C.relator r ++ pathWord C decode fs qs) := by simpa [check, and_assoc] using h
    have hp := pathCheck_sound valid decode fs n prior ps i (fs n).left h'.1
    have hq := pathCheck_sound valid decode fs n prior qs i (fs n).right h'.2.1
    have hr : Holds H g ρ ⟨i, C.relator r, i⟩ := holds_relator i _ (valid.relator r)
    have hall := holds_reduce (holds_append (holds_append (holds_reverse hp) hr rfl) hq rfl)
    have hw := h'.2.2
    simp only [List.append_assoc] at hall hw
    rw [← hw] at hall
    exact hall

def checkChunk [BEq α] [DecidableEq α] (C : Context α) (decode : Nat → Letter α)
    (fs : Nat → FactData α) (ops : Nat → Op) (start count : Nat) : Bool :=
  (List.range count).all fun k => check C decode fs (start+k) (ops (start+k))

theorem chunk_sound [BEq α] [LawfulBEq α] [DecidableEq α]
    {C : Context α} {H : Subgroup G} {g : α → G} {ρ : Nat → G}
    (valid : Valid C H g ρ) (decode : Nat → Letter α) (fs : Nat → FactData α)
    (ops : Nat → Op) (start count : Nat)
    (prior : ∀ n, n < start → Holds H g ρ (fs n))
    (checked : checkChunk C decode fs ops start count = true) :
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
    exact check_sound valid decode fs n (ops n) (fun p hp => ih p hp (by omega)) hc

end Sporadic.Janko3.AmalgamPresentation.Cover.Path
