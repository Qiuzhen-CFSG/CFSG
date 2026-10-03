module

public import Theory.SpecificGroups.UnitaryThree.RootTorus
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# Automorphisms of the Hermitian root group of order 27

Every root automorphism of order eight is conjugate to a scalar action of
an element of order eight in F₉ˣ.

We use coordinates `(x,y,z)` over F₃, identifying them with the Hermitian
point `(x + yi, x² + y² + zi)`. The first two coordinate vectors generate
the group. An endomorphism is therefore determined by their images, and
acts by a two-dimensional matrix, its determinant on the center, and a
linear central correction. For an automorphism of order eight, an explicit
change of coordinates conjugates it to multiplication by `t + i`, where
`t` is the negative matrix trace. The formula is verified by kernel
reduction on the 27² pairs of generator images; no permutations are enumerated.

Source: M. Suzuki, *A characterization of the 3-dimensional projective unitary
group over a finite field of odd characteristic*, J. Algebra 2 (1965),
Section IV, specialized to q = 3.
-/

namespace UnitaryThree.RootAutProof

abbrev K := ZMod 3

@[ext] structure V where
  x : K
  y : K
  z : K
  deriving DecidableEq, Fintype

instance : One V := ⟨⟨0, 0, 0⟩⟩

instance : Mul V := ⟨fun p q => ⟨p.x + q.x, p.y + q.y,
  p.z + q.z + p.y * q.x - p.x * q.y⟩⟩

instance : Inv V := ⟨fun p => ⟨-p.x, -p.y, -p.z⟩⟩

theorem mul_def (p q : V) : p * q = ⟨p.x + q.x, p.y + q.y, p.z + q.z + p.y * q.x - p.x * q.y⟩ := rfl

theorem one_def : (1 : V) = ⟨0, 0, 0⟩ := rfl

theorem inv_def (p : V) : p⁻¹ = ⟨-p.x, -p.y, -p.z⟩ := rfl

instance : Group V where
  mul_assoc p q r := by ext <;> simp only [mul_def] <;> ring
  one_mul p := by ext <;> simp only [mul_def, one_def] <;> ring
  mul_one p := by ext <;> simp only [mul_def, one_def] <;> ring
  inv_mul_cancel p := by ext <;> simp only [mul_def, inv_def, one_def] <;> ring

def e₁ : V := ⟨1, 0, 0⟩

def e₂ : V := ⟨0, 1, 0⟩

def coeff (a b : V) : V →* V where
  toFun p := ⟨a.x * p.x + b.x * p.y, a.y * p.x + b.y * p.y,
    (a.x * b.y - b.x * a.y) * p.z + a.z * p.x + b.z * p.y⟩
  map_one' := by ext <;> simp only [one_def] <;> ring
  map_mul' p q := by ext <;> simp only [mul_def] <;> ring

def det (a b : V) : K := a.x * b.y - b.x * a.y

theorem coeff_injective (a b : V) (hd : det a b ≠ 0) :
    Function.Injective (coeff a b) := by
  intro p q h
  have hx := congrArg V.x h
  have hy := congrArg (fun v : V => v.y) h
  have hz := congrArg (fun v : V => v.z) h
  change a.x * p.x + b.x * p.y = a.x * q.x + b.x * q.y at hx
  change a.y * p.x + b.y * p.y = a.y * q.x + b.y * q.y at hy
  change det a b * p.z + a.z * p.x + b.z * p.y =
    det a b * q.z + a.z * q.x + b.z * q.y at hz
  have h₁ : p.x = q.x := by
    apply (mul_left_cancel₀ hd)
    dsimp [det]
    linear_combination b.y * hx - b.x * hy
  have h₂ : p.y = q.y := by
    apply (mul_left_cancel₀ hd)
    dsimp [det]
    linear_combination a.x * hy - a.y * hx
  have h₃ : p.z = q.z := by
    apply (mul_left_cancel₀ hd)
    rw [h₁, h₂] at hz
    linear_combination hz
  exact V.ext h₁ h₂ h₃

noncomputable def aut (a b : V) (hd : det a b ≠ 0) : MulAut V :=
  MulEquiv.ofBijective (coeff a b) ⟨coeff_injective a b hd,
    Finite.surjective_of_injective (coeff_injective a b hd)⟩

/-- The linear change of basis sends the first coordinate vector to itself
and its image under the given matrix to `(t,1)`, where `t` is minus the trace.
The central correction solves the corresponding equation involving `M + I`;
`k` below is its determinant. -/
def conjA (a b : V) : V :=
  let k := (a.x + 1) * (b.y + 1) - b.x * a.y
  ⟨1, 0, (a.y * b.z - (b.y + 1) * a.z) / (a.y * k)⟩

def conjB (a b : V) : V :=
  let k := (a.x + 1) * (b.y + 1) - b.x * a.y
  ⟨(-(a.x + b.y) - a.x) / a.y, 1 / a.y,
    (b.x * a.z - (a.x + 1) * b.z) / (a.y * k)⟩

def scalar (t : K) : V →* V := coeff ⟨t, 1, 0⟩ ⟨-1, t, 0⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- A finite check of the conjugating formula on pairs of generator images.
The order conditions are tested only on the two generators. -/
theorem census : ∀ a b : V,
    (coeff a b)^[8] e₁ = e₁ → (coeff a b)^[8] e₂ = e₂ →
    ((coeff a b)^[4] e₁ ≠ e₁ ∨ (coeff a b)^[4] e₂ ≠ e₂) →
    det (conjA a b) (conjB a b) ≠ 0 ∧ -(a.x + b.y) ≠ 0 ∧
    (coeff (conjA a b) (conjB a b)) (coeff a b e₁) =
      scalar (-(a.x + b.y)) (coeff (conjA a b) (conjB a b) e₁) ∧
    (coeff (conjA a b) (conjB a b)) (coeff a b e₂) =
      scalar (-(a.x + b.y)) (coeff (conjA a b) (conjB a b) e₂) := by
  decide +kernel

def toRoot (p : V) : Root :=
  ⟨(⟨p.x, p.y⟩, ⟨p.x ^ 2 + p.y ^ 2, p.z⟩), by
    have h : ∀ x y z : K,
        (⟨x ^ 2 + y ^ 2, z⟩ : FiniteField.Nine) + star ⟨x ^ 2 + y ^ 2, z⟩ +
          star ⟨x, y⟩ * ⟨x, y⟩ = 0 := by decide +kernel
    exact h p.x p.y p.z⟩

def fromRoot (p : Root) : V := ⟨p.val.1.re, p.val.1.im, p.val.2.im⟩

def rootEquiv : V ≃* Root where
  toFun := toRoot
  invFun := fromRoot
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

lemma generated (p : V) : ∃ i j k : Fin 3,
    p = e₁ ^ i.val * e₂ ^ j.val * (e₁ * e₂ * e₁⁻¹ * e₂⁻¹) ^ k.val := by
  have h : ∀ p : V, ∃ i j k : Fin 3,
      p = e₁ ^ i.val * e₂ ^ j.val * (e₁ * e₂ * e₁⁻¹ * e₂⁻¹) ^ k.val := by decide +kernel
  exact h p

lemma hom_ext (f g : V →* V) (h₁ : f e₁ = g e₁) (h₂ : f e₂ = g e₂) : f = g := by
  apply MonoidHom.ext
  intro p
  obtain ⟨i, j, k, rfl⟩ := generated p
  simp only [map_mul, map_pow, map_inv, h₁, h₂]

lemma coeff_eq (f : V →* V) : coeff (f e₁) (f e₂) = f := by
  apply hom_ext <;> simp [coeff, e₁, e₂]

lemma aut_pow_apply (f : MulAut V) (n : ℕ) (p : V) : (f ^ n) p = f^[n] p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, ih, Function.iterate_succ_apply]

def fieldScalar (t : K) : FiniteField.Nineˣ :=
  Units.mk0 ⟨t, 1⟩ (by
    intro h
    have := congrArg QuadraticAlgebra.im h
    exact one_ne_zero this)

lemma fieldScalar_order (t : K) (ht : t ≠ 0) : orderOf (fieldScalar t) = 8 := by
  have h : ∀ t : K, t ≠ 0 → (fieldScalar t) ^ 4 ≠ 1 ∧ (fieldScalar t) ^ 8 = 1 := by
    decide +kernel
  obtain ⟨h₄, h₈⟩ := h t ht
  exact orderOf_eq_prime_pow (p := 2) (n := 2) h₄ h₈

lemma scalar_compat : ∀ (t : K) (p : V),
    rootEquiv (scalar t p) = scale (fieldScalar t) (rootEquiv p) := by
  decide +kernel

lemma conjugacy (f : MulAut V) (h₈ : f ^ 8 = 1) (h₄ : f ^ 4 ≠ 1) :
    ∃ (c : MulAut V) (t : K), t ≠ 0 ∧ ∀ p, c (f p) = scalar t (c p) := by
  let a := f e₁
  let b := f e₂
  have he : coeff a b = f.toMonoidHom := coeff_eq f.toMonoidHom
  have hp₈ (p : V) : (coeff a b)^[8] p = p := by
    rw [he]
    change f^[8] p = p
    rw [← aut_pow_apply, h₈]
    rfl
  have hp₄ : (coeff a b)^[4] e₁ ≠ e₁ ∨ (coeff a b)^[4] e₂ ≠ e₂ := by
    by_contra h
    push Not at h
    apply h₄
    apply MulEquiv.toMonoidHom_injective
    apply hom_ext
    · change (f ^ 4) e₁ = e₁
      rw [aut_pow_apply]
      rw [he] at h
      exact h.1
    · change (f ^ 4) e₂ = e₂
      rw [aut_pow_apply]
      rw [he] at h
      exact h.2
  obtain ⟨hd, ht, hc₁, hc₂⟩ := census a b (hp₈ e₁) (hp₈ e₂) hp₄
  let c := aut (conjA a b) (conjB a b) hd
  refine ⟨c, -(a.x + b.y), ht, ?_⟩
  have hc : c.toMonoidHom.comp f.toMonoidHom =
      (scalar (-(a.x + b.y))).comp c.toMonoidHom := by
    apply hom_ext
    · change coeff (conjA a b) (conjB a b) (f e₁) =
        scalar (-(a.x + b.y)) (coeff (conjA a b) (conjB a b) e₁)
      rw [he] at hc₁
      exact hc₁
    · change coeff (conjA a b) (conjB a b) (f e₂) =
        scalar (-(a.x + b.y)) (coeff (conjA a b) (conjB a b) e₂)
      rw [he] at hc₂
      exact hc₂
  exact fun p => DFunLike.congr_fun hc p

end UnitaryThree.RootAutProof

namespace UnitaryThree
open RootAutProof

/-- An order-eight automorphism of the Hermitian root group is conjugate to
multiplication by a generator of the scalar torus. -/
public theorem conjugate_scale_of_orderOf_eq_eight (f : MulAut Root) (hf : orderOf f = 8) :
    ∃ (c : MulAut Root) (r : FiniteField.Nineˣ), orderOf r = 8 ∧
      ∀ p : Root, c (f p) = scale r (c p) := by
  let g : MulAut V := rootEquiv.trans (f.trans rootEquiv.symm)
  have hg (n : ℕ) (p : V) : (g ^ n) p = rootEquiv.symm ((f ^ n) (rootEquiv p)) := by
    induction n generalizing p with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, MulAut.mul_apply, ih, pow_succ, MulAut.mul_apply]
      simp [g]
  have hf₈ : f ^ 8 = 1 := by rw [← hf]; exact pow_orderOf_eq_one f
  have hg₈ : g ^ 8 = 1 := by
    apply MulEquiv.ext
    intro p
    rw [hg, hf₈]
    simp
  have hg₄ : g ^ 4 ≠ 1 := by
    intro h
    have hf₄ : f ^ 4 = 1 := by
      apply MulEquiv.ext
      intro p
      have hh := congrArg (fun k : MulAut V => rootEquiv (k (rootEquiv.symm p))) h
      simpa only [hg, MulEquiv.apply_symm_apply, MulAut.one_apply] using hh
    have := orderOf_dvd_of_pow_eq_one hf₄
    rw [hf] at this
    norm_num at this
  obtain ⟨c, t, ht, hc⟩ := conjugacy g hg₈ hg₄
  refine ⟨rootEquiv.symm.trans (c.trans rootEquiv), fieldScalar t, fieldScalar_order t ht, ?_⟩
  intro p
  have h := congrArg rootEquiv (hc (rootEquiv.symm p))
  simpa only [g, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, scalar_compat] using h

end UnitaryThree
