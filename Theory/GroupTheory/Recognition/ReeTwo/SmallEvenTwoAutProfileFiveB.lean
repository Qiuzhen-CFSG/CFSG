module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutProfilesB

/-!
# Eighth powers in the rank-five profile stabilizers

Each of the four rank-five profiles determines a complete invariant flag.
In the binary coding of `rankFiveProfile`, ordered bases for these flags are
`[3, 4, 1, 8, 16]`, `[1, 8, 6, 2, 16]`, `[1, 4, 10, 2, 16]`, and
`[1, 6, 10, 2, 16]`. The tables below record the least flag dimension containing
each vector. Small kernel-checked identities recover the flag from profile
classes, their products, and a monochromatic coset condition.

A profile-preserving automorphism therefore preserves height. Over the binary
field, the product of two vectors of equal height has smaller height, so
`d(x) = f(x) * x` lowers height and its fifth iterate is trivial. Squaring this
difference operation three times gives `d^[8](x) = f^[8](x) * x`, proving the
certificate without enumerating automorphisms.

Source: the four explicit profiles in `SmallEvenTwoAutProfilesB`, based on
Shinoda (1975), (2.3), pp. 81–82, with the root convention of
`SmallEvenCandidates`. The flag argument uses only these finite profiles.
-/

namespace ReeTwo.SylowModel.SmallEvenAutB
set_option synthInstance.maxSize 4096
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Least dimension of a flag member containing the vector. -/
private def height (i : Fin 4) (x : Binary 5) : ℕ :=
  ((![
    ([0, 3, 3, 1, 2, 3, 3, 2, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] : List ℕ),
    ([0, 1, 4, 4, 4, 4, 3, 3, 2, 2, 4, 4, 4, 4, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] : List ℕ),
    ([0, 1, 4, 4, 2, 2, 4, 4, 4, 4, 3, 3, 4, 4, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] : List ℕ),
    ([0, 1, 4, 4, 4, 4, 2, 2, 4, 4, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] : List ℕ)]) i).getD
    ((x.toAdd 0).val + 2 * (x.toAdd 1).val + 4 * (x.toAdd 2).val +
      8 * (x.toAdd 3).val + 16 * (x.toAdd 4).val) 5

private def flag (i : Fin 4) (k : ℕ) (x : Binary 5) : Prop := height i x ≤ k
private instance (i : Fin 4) (k : ℕ) (x : Binary 5) : Decidable (flag i k x) :=
  inferInstanceAs (Decidable (height i x ≤ k))

/-- Products of two members of a class, using that every element is self-inverse. -/
private def products (p : Binary 5 → Prop) (x : Binary 5) : Prop :=
  ∃ y, p y ∧ p (x * y)
private instance (p : Binary 5 → Prop) [DecidablePred p] (x : Binary 5) :
    Decidable (products p x) := inferInstanceAs (Decidable (∃ y, p y ∧ p (x * y)))

-- In row zero, the two involution classes determine the first three steps.
private theorem row0_one : ∀ x, flag 0 1 x ↔
    products (fun y => rankFiveProfile 0 y = (8, 0, 0)) x := by decide +kernel
private theorem row0_two : ∀ x, flag 0 2 x ↔
    x = 1 ∨ rankFiveProfile 0 x = (0, 8, 0) := by decide +kernel
private theorem row0_three : ∀ x, flag 0 3 x ↔
    products (fun y => y = 1 ∨ rankFiveProfile 0 y = (8, 0, 0) ∨
      rankFiveProfile 0 y = (0, 8, 0)) x := by decide +kernel

-- The unique monochromatic coset determines the hyperplane.
private theorem row0_four : ∀ x, flag 0 4 x ↔
    flag 0 3 x ∨ ∀ y, flag 0 3 y → rankFiveProfile 0 (x * y) = (0, 0, 8) :=
  by decide +kernel

-- In the last three rows, first recover the line and the support hyperplane.
private theorem other_one : ∀ i : Fin 3, ∀ x, flag i.succ 1 x ↔
    x = 1 ∨ rankFiveProfile i.succ x = (0, 4, 4) := by decide +kernel
private theorem other_four : ∀ i : Fin 3, ∀ x, flag i.succ 4 x ↔
    products (fun y => rankFiveProfile i.succ y ≠ (0, 0, 0)) x := by decide +kernel

-- The zero-profile vectors in the hyperplane recover the middle two steps.
private theorem other_two : ∀ i : Fin 3, ∀ x, flag i.succ 2 x ↔
    products (fun y => flag i.succ 4 y ∧ rankFiveProfile i.succ y = (0, 0, 0)) x :=
  by decide +kernel
private theorem other_three : ∀ i : Fin 3, ∀ x, flag i.succ 3 x ↔
    flag i.succ 2 x ∨ (flag i.succ 4 x ∧ rankFiveProfile i.succ x = (0, 0, 0)) :=
  by decide +kernel

private theorem height_le : ∀ i x, height i x ≤ 5 := by decide +kernel
private theorem height_zero : ∀ i x, height i x = 0 ↔ x = 1 := by decide +kernel

/-- Equal-height vectors have the same image in a one-dimensional binary quotient. -/
private theorem height_mul : ∀ i x y, height i x = height i y →
    height i (x * y) ≤ height i x - 1 := by decide +kernel

private theorem products_invariant (f : MulAut (Binary 5)) (p : Binary 5 → Prop)
    (hp : ∀ x, p (f x) ↔ p x) (x : Binary 5) :
    products p (f x) ↔ products p x := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨z, rfl⟩ := f.surjective y
    refine ⟨z, (hp z).mp hy, (hp (x * z)).mp ?_⟩
    simpa only [map_mul] using hxy
  · rintro ⟨y, hy, hxy⟩
    refine ⟨f y, (hp y).mpr hy, ?_⟩
    simpa only [map_mul] using (hp (x * y)).mpr hxy

private theorem flag_invariant (i : Fin 4) (f : MulAut (Binary 5))
    (h : ∀ x, rankFiveProfile i (f x) = rankFiveProfile i x) :
    ∀ k : Fin 6, ∀ x, flag i k (f x) ↔ flag i k x := by
  induction i using Fin.cases with
  | zero =>
    have h1 (x) : flag 0 1 (f x) ↔ flag 0 1 x := by
      simp only [row0_one]
      apply products_invariant
      intro y
      rw [h]
    have h2 (x) : flag 0 2 (f x) ↔ flag 0 2 x := by
      simp only [row0_two, f.map_eq_one_iff, h]
    have h3 (x) : flag 0 3 (f x) ↔ flag 0 3 x := by
      simp only [row0_three]
      apply products_invariant
      intro y
      rw [f.map_eq_one_iff, h]
    have h4 (x) : flag 0 4 (f x) ↔ flag 0 4 x := by
      rw [row0_four, row0_four, h3]
      apply or_congr_right
      constructor
      · intro ht y hy
        have hh := ht (f y) ((h3 y).mpr hy)
        simpa only [← map_mul, h] using hh
      · intro ht y hy
        obtain ⟨z, rfl⟩ := f.surjective y
        have hh := ht z ((h3 z).mp hy)
        simpa only [← map_mul, h] using hh
    intro k x
    fin_cases k
    · simpa only [flag, Nat.le_zero, height_zero] using f.map_eq_one_iff (x := x)
    · exact h1 x
    · exact h2 x
    · exact h3 x
    · exact h4 x
    · exact iff_of_true (height_le _ _) (height_le _ _)
  | succ i =>
    have h1 (x) : flag i.succ 1 (f x) ↔ flag i.succ 1 x := by
      simp only [other_one, f.map_eq_one_iff, h]
    have h4 (x) : flag i.succ 4 (f x) ↔ flag i.succ 4 x := by
      simp only [other_four]
      apply products_invariant
      intro y
      rw [h]
    have h2 (x) : flag i.succ 2 (f x) ↔ flag i.succ 2 x := by
      simp only [other_two]
      apply products_invariant
      intro y
      rw [h4, h]
    have h3 (x) : flag i.succ 3 (f x) ↔ flag i.succ 3 x := by
      simp only [other_three, h2, h4, h]
    intro k x
    fin_cases k
    · simpa only [flag, Nat.le_zero, height_zero] using f.map_eq_one_iff (x := x)
    · exact h1 x
    · exact h2 x
    · exact h3 x
    · exact h4 x
    · exact iff_of_true (height_le _ _) (height_le _ _)

private theorem height_invariant (i : Fin 4) (f : MulAut (Binary 5))
    (h : ∀ x, rankFiveProfile i (f x) = rankFiveProfile i x) (x : Binary 5) :
    height i (f x) = height i x := by
  have hf := flag_invariant i f h
  apply Nat.le_antisymm
  · exact (hf ⟨height i x, Nat.lt_succ_of_le (height_le i x)⟩ x).mpr (le_refl _)
  · exact (hf ⟨height i (f x), Nat.lt_succ_of_le (height_le i (f x))⟩ x).mp (le_refl _)

private theorem self_mul : ∀ x : Binary 5, x * x = 1 := by decide +kernel

private def difference (f : Binary 5 →* Binary 5) : Binary 5 →* Binary 5 :=
  f * MonoidHom.id _

/-- In characteristic two, squaring the difference replaces the map by its square. -/
private theorem difference_square (f : Binary 5 →* Binary 5) :
    (difference f).comp (difference f) = difference (f.comp f) := by
  apply MonoidHom.ext
  intro x
  change f (f x * x) * (f x * x) = f (f x) * x
  rw [map_mul]
  calc
    f (f x) * f x * (f x * x) = (f (f x) * x) * (f x * f x) := by ac_rfl
    _ = f (f x) * x := by rw [self_mul, mul_one]

private theorem difference_eight (f : Binary 5 →* Binary 5) (x : Binary 5) :
    (difference f)^[8] x = f (f (f (f (f (f (f (f x))))))) * x := by
  let d := difference f
  have hh : ((d.comp d).comp (d.comp d)).comp ((d.comp d).comp (d.comp d)) =
      difference (((f.comp f).comp (f.comp f)).comp ((f.comp f).comp (f.comp f))) := by
    simp only [d, difference_square]
  exact congrArg (fun g : Binary 5 →* Binary 5 => g x) hh

/-- Every automorphism preserving one of the four rank-five profiles has eighth power one. -/
public theorem rankFiveProfileCertificate : RankFiveProfileCertificate := by
  intro i f h
  let d := difference f.toMonoidHom
  have hd (x) : height i (d x) ≤ height i x - 1 := by
    change height i (f x * x) ≤ height i x - 1
    have hh := height_mul i (f x) x (height_invariant i f h x)
    rwa [height_invariant i f h x] at hh
  have hiter (n : ℕ) (x : Binary 5) : height i (d^[n] x) ≤ height i x - n := by
    induction n with
    | zero => exact le_refl _
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hh := hd (d^[n] x)
      omega
  apply MulEquiv.ext
  intro x
  change (f ^ 8) x = x
  have hz : d^[8] x = 1 := (height_zero i _).mp (by
    have hh := hiter 8 x
    have hx := height_le i x
    omega)
  have he := difference_eight f.toMonoidHom x
  change d^[8] x = (f ^ 8) x * x at he
  rw [hz] at he
  have hh := congrArg (fun y => y * x) he
  simpa only [one_mul, mul_assoc, self_mul, mul_one] using hh.symm

end ReeTwo.SylowModel.SmallEvenAutB
