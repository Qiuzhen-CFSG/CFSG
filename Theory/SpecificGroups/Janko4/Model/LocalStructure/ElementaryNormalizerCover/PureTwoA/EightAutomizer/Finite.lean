module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Tables

/-!
# Exhaustion of the selected elementary-eight automizer

An automorphism preserving XOR, the native sixteen, and the two involution
colors is sifted along the ordered eight-element base. The 64 checked
transversals correct one basis image at each step, and XOR linearity finishes
the argument. Thus every permitted action is a positive word in the three
literal generators. Explicit orbit words give the three nonzero orbits with
representatives 3, 64, and 1; pairs in the last orbit span all eight directions.
Source: Kleidman--Wilson (1988), Section 2.1, the elementary-eight case.
-/

@[expose] public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer

theorem transversal_word (j : Fin 64) :
    wordAction (transversalWord j) = linear (transversalColumns j) :=
  xor_hom_ext _ _ (word_good _).zero (linear_zero _)
    (word_good _).map_xor (linear_xor _) (transversal_word_basis j)

private def Fixes (e : Mask → Mask) (n : ℕ) : Prop :=
  ∀ x ∈ prefixSpan n, e x = x

private theorem candidate_of_good {e : Mask → Mask} (he : Good e) (n : Fin 8)
    (hfix : Fixes e n.val) : Candidate n.val (e (siftingBasis n.val)) := by
  apply List.all_eq_true.mpr
  intro y hy
  apply decide_eq_true_iff.mpr
  have h := he.map_xor (siftingBasis n.val) y
  rw [hfix y hy] at h
  rw [← h]
  exact ⟨he.map_inK _, he.map_color _⟩

private theorem fixes_succ {e : Mask → Mask} (he : Good e) (n : Fin 8)
    (hfix : Fixes e n.val) (hb : e (siftingBasis n.val) = siftingBasis n.val) : Fixes e (n.val+1) := by
  intro x hx
  rw [prefix_succ n] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hfix x hx
  · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    rw [he.map_xor, hb, hfix y hy]

private theorem correct_one {e : Mask → Mask} (he : Good e) (n : Fin 8)
    (hfix : Fixes e n.val) :
    ∃ w : List (Fin 3), Fixes (wordAction w ∘ e) (n.val+1) := by
  obtain ⟨j,hjn,hjt⟩ := candidate_covered n _ (candidate_of_good he n hfix)
  have hTfix (y : Mask) (hy : y ∈ prefixSpan n.val) :
      wordAction (transversalWord j) y = y := by
    rw [transversal_word]
    exact transversal_fixes j y (by simpa only [hjn] using hy)
  have hTbase : wordAction (transversalWord j) (siftingBasis n.val) =
      e (siftingBasis n.val) := by
    rw [transversal_word]
    simpa only [hjn, hjt] using transversal_image j
  let u := inverseWord (transversalWord j)
  have hIfix (y : Mask) (hy : y ∈ prefixSpan n.val) : wordAction u y = y := by
    calc
      wordAction u y = wordAction u (wordAction (transversalWord j) y) :=
        congrArg (wordAction u) (hTfix y hy).symm
      _ = y := word_inverse _ y
  refine ⟨u, fixes_succ ((word_good u).comp he) n ?_ ?_⟩
  · intro y hy
    dsimp only [Function.comp_def]
    rw [hfix y hy]
    exact hIfix y hy
  · dsimp only [Function.comp_def]
    rw [← hTbase]
    exact word_inverse _ _

private theorem correction (e : Mask → Mask) (he : Good e) (n : ℕ) (hn : n ≤ 8) :
    ∃ w : List (Fin 3), Fixes (wordAction w ∘ e) n := by
  induction n with
  | zero =>
    refine ⟨[], ?_⟩
    intro x hx
    have hx0 : x = 0 := List.mem_singleton.mp hx
    subst x
    exact he.zero
  | succ n ih =>
    obtain ⟨w,hw⟩ := ih (Nat.le_trans (Nat.le_succ n) hn)
    have hn8 : n < 8 := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
    obtain ⟨v,hv⟩ := correct_one ((word_good w).comp he) ⟨n,hn8⟩ hw
    refine ⟨v ++ w, ?_⟩
    intro x hx
    simpa only [Function.comp_apply, wordAction_append] using hv x hx

/-- Every bijective XOR map preserving the native sixteen and the involution
color is a positive word in the three certified actions. The proof sifts along
an eight-point base with orbit factors 15, 14, 12, 8, 8, 4, 2, 1. -/
theorem exhaustion_of_good (e : Mask → Mask) (he : Good e) :
    ∃ w : List (Fin 3), ∀ x, wordAction w x = e x := by
  obtain ⟨w,hw⟩ := correction e he 8 le_rfl
  refine ⟨inverseWord w, ?_⟩
  intro x
  have h := word_inverse w (e x)
  have hc := (word_good w).comp he
  have hid : wordAction w ∘ e = id :=
    xor_hom_ext _ _ hc.zero rfl hc.map_xor (fun _ _ => rfl)
      (fun i => hw (bitBasis i) (bitBasis_mem_prefix i))
  have hx : wordAction w (e x) = x := congrFun hid x
  rw [hx] at h
  exact h

theorem exhaustion (e : Mask → Mask) (he : Function.Bijective e)
    (hxor : ∀ x y, e (xor x y) = xor (e x) (e y))
    (hK : ∀ x, inK (e x) = inK x)
    (hq : ∀ x, orbitColor (e x) = orbitColor x) :
    ∃ w : List (Fin 3), ∀ x, wordAction w x = e x := by
  apply exhaustion_of_good e
  refine ⟨?_, hxor, he.1, hK, hq⟩
  simpa only [xor_zero, xor_self] using hxor 0 0

/-- The invariant sixteen, the first color outside it, and the second color
are the three nonzero orbits. This is a finite label, independent of matrix ranks. -/
def orbitRepresentative (x : Mask) : Mask :=
  if inK x then 3 else if orbitColor x then 64 else 1

def orbitWord (x : Mask) : List (Fin 3) := (#[[], [], [2], [], [1, 0, 1], [1, 2, 2, 0], [2, 0, 1, 2, 0], [1, 0, 1, 2], [0, 2, 1, 2, 1, 2, 0], [0, 2, 0], [2, 0, 2, 0], [0, 2, 2, 2, 0, 2, 1, 0], [1, 2, 0, 2, 0], [2, 1, 0, 1], [2, 1, 0, 1, 2], [0, 1, 2, 0], [1, 2, 1, 2, 1, 0], [2, 0], [2, 2, 2, 1, 2], [1, 0, 1, 0, 2, 0, 2], [0, 2, 2, 2, 1], [0, 1, 2, 0, 2], [2, 1, 2, 1, 0], [2, 2, 0, 1, 2], [2, 0, 2], [1, 2, 2, 2, 0], [0, 2, 1, 0, 2], [1, 2, 1, 2, 2, 0, 1], [0, 2, 0, 1, 0, 2, 2], [2, 2, 2, 0, 1], [0, 1, 2, 1, 0, 2, 2], [1, 2, 1, 2, 0], [1, 2, 2, 2, 0, 1], [0, 2, 1, 2], [2, 1, 2, 2], [0, 2, 1, 2, 1, 0], [1, 2, 1, 2], [2, 0, 1, 2, 2, 1], [2, 1, 2, 2, 0, 1], [2, 1, 2, 2, 2], [1, 0, 2, 0, 2, 1], [2, 0, 1, 0, 2, 2], [2, 1, 0], [2, 0, 2, 1], [2, 2, 2, 1, 0, 2], [1, 2, 0, 2, 1], [2, 1, 0, 2, 2, 1], [2, 1, 0, 2], [2, 1, 0, 2, 2, 2, 0], [0, 1, 2, 2, 0], [1, 0, 1, 0, 1], [2, 1, 2, 1, 0, 2], [0], [2, 1, 2, 1, 0, 2, 2], [1, 2, 1, 0, 1], [2, 0, 2, 1, 0], [2, 2, 1, 2, 0], [2, 0, 2, 0, 2], [0, 1, 2], [2, 0, 2, 2, 2, 1, 0, 2], [1], [0, 1, 2, 2, 0, 2], [2, 2, 2, 0, 2, 1, 0], [1, 2, 1, 2, 2, 0], [], [0, 1, 2, 1], [2, 2, 0, 1, 2, 1], [2, 2], [1, 2, 2, 2, 0], [0, 2, 2, 1], [1, 0, 2, 0, 1], [2, 1, 2, 2, 2, 0], [2, 0, 1, 2, 1], [2, 2, 2], [2], [0, 1, 2, 0, 1, 2], [2, 1, 0, 2, 1], [0, 2, 2, 1, 0, 1], [1, 0, 2, 0, 2, 1, 2], [1, 0, 2, 1], [0, 2, 2, 0, 2, 1, 0], [2, 0, 1], [0, 2, 0, 2, 1, 2], [1, 2, 0, 2, 1, 0], [1, 2, 0, 1, 2, 1], [2, 0, 2, 1, 2, 2, 0], [2, 0, 1, 0, 1], [0, 1], [2, 0, 1, 2, 1, 0, 1], [2, 2, 0, 1, 2, 0, 2], [2, 1, 0], [0, 1, 2], [0, 2, 0, 1, 2, 2, 0], [2, 1, 2], [2, 2, 2, 0], [1, 2, 2, 0], [1, 0, 2], [1, 0, 2, 2, 1, 2], [1, 0, 2, 2, 1], [2, 2, 1, 0, 2], [1, 2, 2], [0, 2, 0, 2, 2, 2, 0], [2, 0, 2, 1, 2, 1, 0], [2, 0, 2, 1, 2], [1, 2, 2, 2], [0, 1, 2, 2, 1], [1, 2, 2, 0, 1], [0, 2, 2, 2, 0], [1, 0], [2, 1, 0, 2, 0, 2, 1], [0, 2, 1], [0, 1, 0, 2, 2], [2, 2, 1], [2, 2, 0, 1, 2, 2, 0, 2], [2, 0, 2, 1, 0], [2, 0, 2, 2, 1, 2], [1, 2, 0, 2, 1, 2, 2, 0], [2, 2, 0, 1, 2], [0, 2, 2], [1, 2, 0], [2, 2, 0], [2, 0, 1, 2, 2], [0, 1, 0, 2, 1], [2, 2, 2, 0, 2, 1, 0], [0, 2, 2, 2], [1, 2, 1, 0, 1, 0, 1], [2, 2, 0, 1, 2, 2, 0], [2, 1, 0, 1, 2, 1], [1], [2, 1, 2, 2, 0], [1, 2, 2, 0], [0, 1, 2, 2, 0], [0, 2, 0, 2, 1, 0], [0], [2, 2, 0], [1, 2, 0, 2, 0, 2], [1, 2, 2, 2, 0, 1, 2], [1, 2, 0], [2, 1, 2, 0], [1, 2, 1, 2, 1, 0, 2], [1, 0, 2, 0], [2, 0, 2, 0, 2, 1, 0], [1, 2, 2, 0, 2], [2, 0], [1, 0, 1, 2, 0, 2], [2, 2, 0, 2, 2, 1, 2], [2, 2, 2, 1], [2, 2, 0, 2, 1, 0], [1, 0, 2, 2, 2, 0], [1, 2, 2, 0, 2, 1, 0], [0, 1, 0, 2, 0, 2], [1, 2, 1, 0, 2], [1, 2, 1, 0, 2, 2], [0, 2, 1, 0], [2, 2, 2, 0], [2, 0, 1, 0, 2, 1], [2, 1, 2, 0], [2, 2, 2, 0, 1, 2], [0, 2, 0, 2], [0, 2, 2, 2, 1, 0, 2], [2, 1, 0, 2, 2, 2], [1, 2, 1, 2, 2], [2, 1], [1, 0, 2, 0, 2], [2, 2, 2, 1, 2], [2, 1, 0, 2, 2], [1, 2, 0, 2], [2, 1, 2], [1, 2, 0, 2, 0, 1], [0, 2, 1, 2, 0], [0, 1, 2, 2, 2, 0], [2, 0, 2, 1, 2], [0, 1, 2, 1, 2, 0], [0, 2, 0, 2, 1], [2, 0, 2, 0, 1], [0, 2, 2, 2, 0], [0, 1, 2, 1, 0, 1], [1, 0], [2, 0, 1, 2, 0, 2], [2, 2, 2, 0, 1, 2], [0, 2, 1, 2, 2, 0], [2, 2, 0, 2], [1, 2, 1, 0, 1, 2], [0, 1, 0, 1], [0, 2, 0, 2, 0, 2, 1, 0], [1, 0, 2, 0, 2, 1, 0], [0, 1], [2, 1, 2, 1, 2, 0], [1, 2], [0, 2, 1, 0, 1, 2], [0, 1, 2, 1, 2, 1, 0, 2], [2, 2, 0], [2, 0, 2, 0, 1, 2], [2, 2, 2, 1, 0, 1], [2, 1, 0, 1], [1, 2, 0, 2, 1, 2], [2, 1, 2, 1], [0, 2, 2, 1, 2], [0, 2, 2, 0, 1, 2], [1, 2, 1], [1, 0, 1], [0, 2, 0, 1, 2], [1, 2, 2, 1, 2], [2, 2, 1, 0, 1], [1, 0, 1, 0, 1, 2, 1], [1, 2, 0, 1, 2], [1, 2, 0, 1], [1, 2, 1, 0, 2, 0, 2, 1], [2, 2, 2, 1, 2, 0], [2, 0, 1, 2], [2, 2, 0, 2, 0, 2], [2, 2, 0, 2, 2, 2, 1, 0, 2], [2, 1, 2, 1, 0, 1], [2, 0], [2, 2, 0, 2, 1, 0], [0, 1, 2, 2], [1, 0, 1, 2, 1], [2, 1, 0, 1, 0, 1], [2, 0, 1, 2, 2, 0], [0, 1, 2, 2, 2], [0, 2, 1, 0], [2, 1], [0, 2, 2, 1, 2], [2, 0, 1, 2, 2, 0, 2], [2, 0, 1, 2, 1, 2, 0], [2, 2, 0, 2, 0, 1], [0, 2, 0, 1], [2, 0, 2, 2, 2, 0], [1], [1, 0, 2, 2, 2], [1, 2, 0, 1, 2], [2, 1, 2, 1, 2, 2], [1, 2], [1, 0, 2, 2], [2, 2, 1, 0, 2, 2], [2, 2, 1, 2], [1, 2, 2, 1, 2], [0, 1, 0, 1, 2, 1], [0, 2, 1, 2], [1, 2, 2, 1], [2, 2, 1, 2], [2, 1, 2, 2, 0], [1, 0, 2, 2, 0, 2, 1, 0], [0], [0, 2, 0, 2, 1, 0], [2, 2, 0, 1], [2, 0, 2, 0, 2, 1, 2], [1, 2, 2, 0, 2, 1, 0], [1, 0, 2, 0, 1, 2, 2, 0], [0, 2], [2, 1, 2, 0, 1, 2, 1], [1, 0, 2, 1, 0], [2, 0, 1, 2], [1, 2, 0, 1, 2, 2, 0], [1, 2, 1, 0], [0, 2, 1, 0, 2, 1]] : Array (List (Fin 3))).getD x.val []

/-- An explicit positive word carries the appropriate representative to every
nonzero mask. -/
theorem orbit_word : ∀ x : Mask, x ≠ 0 →
    wordAction (orbitWord x) (orbitRepresentative x) = x := by decide +kernel

def secondColorPairs (i : Fin 8) : Mask × Mask := (#[(146, 147), (16, 18), (16, 20), (32, 40), (2, 18), (8, 40), (1, 65), (18, 146)] : Array (Mask × Mask)).getD i.val (0,0)

/-- The second-color orbit spans all eight standard mask directions. -/
theorem second_color_spans : ∀ i : Fin 8,
    (secondColorPairs i).1 ≠ 0 ∧ (secondColorPairs i).2 ≠ 0 ∧
    orbitRepresentative (secondColorPairs i).1 = 1 ∧
    orbitRepresentative (secondColorPairs i).2 = 1 ∧
    xor (secondColorPairs i).1 (secondColorPairs i).2 = bitBasis i := by decide +kernel

theorem bitBasis_val : ∀ i : Fin 8, (bitBasis i).val = 2^i.val := by decide +kernel

theorem generator_bitBasis : ∀ (j : Fin 3) (i : Fin 8),
    generator j (bitBasis i) = generatorColumns j i := by decide +kernel


/-- Every nonzero member of the native sixteen has the first color. -/
theorem inK_color : ∀ x : Mask, x ≠ 0 → inK x = true → orbitColor x = true := by decide +kernel

/-- The second color is one nonzero orbit, represented by mask one. -/
theorem second_color_orbit (x : Mask) (hx : x ≠ 0) (hq : orbitColor x = false) :
    wordAction (orbitWord x) 1 = x := by
  cases hK : inK x with
  | false => simpa only [orbitRepresentative, hK, hq, Bool.false_eq_true, if_false] using orbit_word x hx
  | true =>
    have h := inK_color x hx hK
    rw [hq] at h
    cases h

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer
