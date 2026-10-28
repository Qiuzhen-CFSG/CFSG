module

public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
public import Theory.LinearAlgebra.PackedBinaryRows

/-!
# Solution-preserving packed binary elimination

Selecting a row and adding it to selected other rows preserves the solution
space of a homogeneous binary system. Iterating this operation justifies
finite row-reduction certificates without trusting their generator. The
concrete consumer is the degree-1408 HS restriction, whose original tables
and ATLAS attribution are described in `../../source/README.md`.
-/

@[expose] public section

open Thompson.BinaryMatrix
namespace PackedBinaryRows

def solutions (n : ℕ) (rs : List ℕ) (w : Fin n → ZMod 2) : Prop :=
  ∀ r ∈ rs, (fun i : Fin n => bit r i.val) ⬝ᵥ w = 0

lemma solutions_nil (n : ℕ) (w : Fin n → ZMod 2) : solutions n [] w := by
  simp [solutions]

lemma solutions_cons (n : ℕ) (r : ℕ) (rs : List ℕ) (w : Fin n → ZMod 2) :
    solutions n (r :: rs) w ↔
      (fun i : Fin n => bit r i.val) ⬝ᵥ w = 0 ∧ solutions n rs w := by
  simp [solutions]

lemma solutions_zero_cons (n : ℕ) (rs : List ℕ) (w : Fin n → ZMod 2) :
    solutions n (0 :: rs) w ↔ solutions n rs w := by
  simp [solutions_cons, bit]

/-- Select a row using the supplied bit mask, or add a harmless zero row. -/
def pick (j : ℕ) : List ℕ → ℕ × List ℕ
  | [] => (0, [])
  | r :: rs => if r / j % 2 == 1 then (r, rs)
      else let t := pick j rs; (t.1, r :: t.2)

lemma solutions_pick (n j : ℕ) (rs : List ℕ) (w : Fin n → ZMod 2) :
    solutions n ((pick j rs).1 :: (pick j rs).2) w ↔ solutions n rs w := by
  induction rs with
  | nil => simp [pick, solutions_zero_cons]
  | cons r rs ih =>
    simp only [pick]
    split
    · rfl
    · simp only [solutions_cons] at ih ⊢
      tauto

def clear (j p r : ℕ) : ℕ := if r / j % 2 == 1 then r ^^^ p else r

lemma dot_xor (n x y : ℕ) (w : Fin n → ZMod 2) :
    (fun i : Fin n => bit (x ^^^ y) i.val) ⬝ᵥ w =
      (fun i : Fin n => bit x i.val) ⬝ᵥ w +
      (fun i : Fin n => bit y i.val) ⬝ᵥ w := by
  simp only [bit_xor]
  exact add_dotProduct _ _ _

lemma solutions_clear (n j p : ℕ) (rs : List ℕ) (w : Fin n → ZMod 2)
    (hp : (fun i : Fin n => bit p i.val) ⬝ᵥ w = 0) :
    solutions n (rs.map (clear j p)) w ↔ solutions n rs w := by
  simp only [solutions, List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h r hr
    have hh := h (clear j p r) r hr rfl
    unfold clear at hh
    split at hh
    · simpa only [dot_xor, hp, add_zero] using hh
    · exact hh
  · intro h r x hx hr
    subst r
    unfold clear
    split
    · simpa only [dot_xor, hp, add_zero] using h x hx
    · exact h x hx

abbrev State := List ℕ × List ℕ

def stateSolutions (n : ℕ) (s : State) (w : Fin n → ZMod 2) : Prop :=
  solutions n s.1 w ∧ solutions n s.2 w

def step (j : ℕ) (s : State) : State :=
  let t := pick j s.2
  (t.1 :: s.1.map (clear j t.1), t.2.map (clear j t.1))

lemma stateSolutions_step (n j : ℕ) (s : State) (w : Fin n → ZMod 2) :
    stateSolutions n (step j s) w ↔ stateSolutions n s w := by
  have h := solutions_pick n j s.2 w
  simp only [solutions_cons] at h
  simp only [stateSolutions, step, solutions_cons]
  constructor
  · rintro ⟨⟨hp, hd⟩, ht⟩
    exact ⟨(solutions_clear n j _ _ w hp).mp hd,
      h.mp ⟨hp, (solutions_clear n j _ _ w hp).mp ht⟩⟩
  · rintro ⟨hd, ht⟩
    obtain ⟨hp, ht⟩ := h.mpr ht
    exact ⟨⟨hp, (solutions_clear n j _ _ w hp).mpr hd⟩,
      (solutions_clear n j _ _ w hp).mpr ht⟩

/-- Double the supplied bit mask after each elimination step. -/
def steps (j : ℕ) : ℕ → State → State
  | 0, s => s
  | k+1, s => steps (j*2) k (step j s)

lemma stateSolutions_steps (n j k : ℕ) (s : State) (w : Fin n → ZMod 2) :
    stateSolutions n (steps j k s) w ↔ stateSolutions n s w := by
  induction k generalizing j s with
  | zero => rfl
  | succ k ih => exact (ih (j*2) (step j s)).trans (stateSolutions_step n j s w)

end PackedBinaryRows
