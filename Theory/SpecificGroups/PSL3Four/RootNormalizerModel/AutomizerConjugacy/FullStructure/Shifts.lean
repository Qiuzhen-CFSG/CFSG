module

public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.AutomizerConjugacy.Reduction

/-!
# Central additive shifts of UT₃(F₄)

An additive map ℓ : F₄² → F₄ gives the automorphism
(x,y,c) ↦ (x,y,c+ℓ(x,y)). These shifts form a finite two-group.
A shift belongs to the inner subgroup precisely when ℓ(x,y)=ay−xb.
Conjugating by the two diagonal factors separately proves that a shift
normalizing the inner–torus join is inner. This is the shift part of the
root-automorphism normalizer calculation; it assumes no classification of
arbitrary root automorphisms.

Source motivation: Aschbacher, *Sporadic Groups* (1994), 8.15, 46.3, 46.14.
The consumer is `FullStructure.normalizer_innerTorus_le_of_coverage`.
-/

@[expose] public section

open Subgroup
namespace Matrix.PSL3Four.RootNormalizerModel.AutomizerConjugacy.FullStructure
noncomputable section

abbrev Shift := (F × F) →+ F

def shift (l : Shift) : MulAut Root where
  toFun q := ⟨q.x, q.y, q.c + l (q.x, q.y)⟩
  invFun q := ⟨q.x, q.y, q.c - l (q.x, q.y)⟩
  left_inv q := by apply SylowModel.U.ext <;> simp
  right_inv q := by apply SylowModel.U.ext <;> simp
  map_mul' q r := by
    apply SylowModel.U.ext
    · rfl
    · rfl
    · change q.c + r.c + q.x * r.y + l ((q.x, q.y) + (r.x, r.y)) =
        q.c + l (q.x, q.y) + (r.c + l (r.x, r.y)) + q.x * r.y
      rw [map_add]
      ring

@[simp] theorem shift_x (l : Shift) (q : Root) : (shift l q).x = q.x := rfl
@[simp] theorem shift_y (l : Shift) (q : Root) : (shift l q).y = q.y := rfl
@[simp] theorem shift_c (l : Shift) (q : Root) :
    (shift l q).c = q.c + l (q.x, q.y) := rfl

theorem shift_injective : Function.Injective shift := by
  intro l m h
  ext p
  have hc := congrArg (fun a : MulAut Root => (a ⟨p.1, p.2, 0⟩).c) h
  simpa using hc

instance : Finite Shift := Finite.of_injective shift shift_injective

theorem shift_add (l m : Shift) : shift (l + m) = shift l * shift m := by
  apply MulEquiv.ext
  intro q
  apply SylowModel.U.ext
  · rfl
  · rfl
  · change q.c + (l (q.x, q.y) + m (q.x, q.y)) =
      (q.c + m (q.x, q.y)) + l (q.x, q.y)
    ring

@[simp] theorem shift_zero : shift 0 = 1 := by
  apply MulEquiv.ext
  intro q
  apply SylowModel.U.ext <;> simp

def shiftHom : Multiplicative Shift →* MulAut Root where
  toFun l := shift l.toAdd
  map_one' := shift_zero
  map_mul' := shift_add

theorem shift_isPGroup : IsPGroup 2 (Multiplicative Shift) := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro l
  refine ⟨1, ?_⟩
  rw [pow_one, pow_two]
  change l.toAdd + l.toAdd = 0
  ext p
  exact CharTwo.add_self_eq_zero _

theorem shift_card : ∃ n, Nat.card Shift = 2 ^ n := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact shift_isPGroup.exists_card_eq

theorem conj_coordinates (r q : Root) :
    MulAut.conj r q = ⟨q.x, q.y, q.c + (r.x * q.y - q.x * r.y)⟩ := by
  apply SylowModel.U.ext
  · change (r.x + q.x) + -r.x = q.x
    ring
  · change (r.y + q.y) + -r.y = q.y
    ring
  · change (r.c + q.c + r.x * q.y) + (r.x * r.y - r.c) +
      (r.x + q.x) * -r.y = q.c + (r.x * q.y - q.x * r.y)
    ring

theorem shift_mem_inner_iff (l : Shift) : shift l ∈ inner ↔
    ∃ a b : F, ∀ x y : F, l (x, y) = a * y - x * b := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r.x, r.y, fun x y => ?_⟩
    have hc := congrArg (fun a : MulAut Root => (a ⟨x, y, 0⟩).c) hr
    simpa only [conj_coordinates, shift_c, zero_add] using hc.symm
  · rintro ⟨a, b, h⟩
    refine ⟨⟨a, b, 0⟩, ?_⟩
    apply MulEquiv.ext
    intro q
    rw [conj_coordinates]
    apply SylowModel.U.ext
    · rfl
    · rfl
    · exact congrArg (q.c + ·) (h q.x q.y).symm

theorem innerTorus_normal_form {s : MulAut Root} (hs : s ∈ innerTorus) :
    ∃ (r : Root) (a : Fˣ × Fˣ), s = MulAut.conj r * diagonalHom a := by
  obtain ⟨i, hi, t, ht, h⟩ := Subgroup.mem_sup_of_normal_left.mp hs
  obtain ⟨r, rfl⟩ := hi
  obtain ⟨a, rfl⟩ := ht
  exact ⟨r, a, h.symm⟩

theorem shift_mem_innerTorus_iff (l : Shift) : shift l ∈ innerTorus ↔ shift l ∈ inner := by
  constructor
  · intro h
    obtain ⟨r, a, hr⟩ := innerTorus_normal_form h
    have hx := congrArg (fun s : MulAut Root => (s ⟨1, 0, 0⟩).x) hr
    have hy := congrArg (fun s : MulAut Root => (s ⟨0, 1, 0⟩).y) hr
    simp only [MulAut.mul_apply, conj_coordinates] at hx hy
    have ha : a = 1 := by
      apply Prod.ext <;> apply Units.ext
      · simpa [diagonalHom, diagonal] using hx.symm
      · simpa [diagonalHom, diagonal] using hy.symm
    rw [ha, map_one, mul_one] at hr
    exact ⟨r, hr.symm⟩
  · intro h; exact (le_sup_left : inner ≤ innerTorus) h

theorem shift_normalizer_equation (l : Shift)
    (hl : shift l ∈ normalizer (innerTorus : Set (MulAut Root)))
    (d : Fˣ × Fˣ) : ∃ r : Root, ∀ x y : F,
      l ((d.1 : F) * x, (d.2 : F) * y) - (d.1 * d.2 : F) * l (x, y) =
        r.x * ((d.2 : F) * y) - ((d.1 : F) * x) * r.y := by
  have hd : diagonalHom d ∈ innerTorus := (le_sup_right : torus ≤ innerTorus) ⟨d, rfl⟩
  obtain ⟨r, a, ha⟩ := innerTorus_normal_form
    ((mem_normalizer_iff.mp hl (diagonalHom d)).mp hd)
  have hda : d = a := by
    have hx := congrArg (fun s : MulAut Root => (s ⟨1, 0, 0⟩).x) ha
    have hy := congrArg (fun s : MulAut Root => (s ⟨0, 1, 0⟩).y) ha
    simp only [MulAut.mul_apply, conj_coordinates] at hx hy
    apply Prod.ext <;> apply Units.ext
    · simpa [shift, diagonalHom, diagonal] using hx
    · simpa [shift, diagonalHom, diagonal] using hy
  subst a
  refine ⟨r, fun x y => ?_⟩
  have hc := congrArg (fun s : MulAut Root => (s ⟨x, y, 0⟩).c) ha
  simp only [MulAut.mul_apply, conj_coordinates] at hc
  simpa [shift, diagonalHom, diagonal,
    sub_eq_add_neg, add_comm] using hc

theorem shift_normalizer_iff (l : Shift) :
    shift l ∈ normalizer (innerTorus : Set (MulAut Root)) ↔ shift l ∈ inner := by
  constructor
  · intro hl
    obtain ⟨u, hu⟩ := exists_fieldFrobenius_ne
    have hu0 : u ≠ 0 := by intro h; subst u; simp at hu
    have hu1 : u ≠ 1 := by intro h; subst u; simp at hu
    let v : Fˣ := Units.mk0 u hu0
    have hv : (1 - u : F) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
    obtain ⟨r, hr⟩ := shift_normalizer_equation l hl (v, 1)
    obtain ⟨s, hs⟩ := shift_normalizer_equation l hl (1, v)
    have hg (y : F) : l (0, y) = l (0, 1) * y := by
      have hy : l (0, y) - u * l (0, y) = r.x * y := by simpa [v] using hr 0 y
      have h1 : l (0, 1) - u * l (0, 1) = r.x := by simpa [v] using hr 0 1
      apply mul_left_cancel₀ hv
      calc
        (1 - u) * l (0, y) = r.x * y := by linear_combination hy
        _ = (1 - u) * (l (0, 1) * y) := by rw [← h1]; ring
    have hf (x : F) : l (x, 0) = x * l (1, 0) := by
      have hx : l (x, 0) - u * l (x, 0) = -(x * s.y) := by simpa [v] using hs x 0
      have h1 : l (1, 0) - u * l (1, 0) = -s.y := by simpa [v] using hs 1 0
      apply mul_left_cancel₀ hv
      calc
        (1 - u) * l (x, 0) = -(x * s.y) := by linear_combination hx
        _ = (1 - u) * (x * l (1, 0)) := by linear_combination -x * h1
    apply (shift_mem_inner_iff l).mpr
    refine ⟨l (0, 1), -l (1, 0), fun x y => ?_⟩
    have he : (x, y) = (x, 0) + (0, y) := by simp
    rw [he, map_add, hf, hg]
    ring
  · intro hl
    exact innerTorus.le_normalizer ((le_sup_left : inner ≤ innerTorus) hl)

end
end Matrix.PSL3Four.RootNormalizerModel.AutomizerConjugacy.FullStructure
