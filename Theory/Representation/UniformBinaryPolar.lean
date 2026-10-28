module
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic

/-!
# Uniform binary pairings on a doubly transitive orbit

An invariant alternating form on a spanning orbit has the same coefficient
on every pair of distinct orbit points. Its pullback is the off-diagonal-one
matrix, whose radical has dimension at most one. A totally singular subspace
of codimension m therefore bounds the orbit degree by 2m+1.

The field-two projective-line application gives f=2 or f=3 from a Borel
orbit of size 2^f+1. This is the linear branch of Aschbacher–Smith 14.2.16,
printed pp.985–986.
-/

public section
open Module
namespace UniformBinaryPolar
variable {n : ℕ}
abbrev V (n : ℕ) := Fin n → ZMod 2

def form (n : ℕ) : LinearMap.BilinForm (ZMod 2) (V n) :=
  Matrix.toBilin' (Matrix.of fun i j : Fin n => if i = j then 0 else 1)

private theorem form_basis (x : V n) (j : Fin n) :
    form n x (Pi.single j 1) = (∑ i, x i) + x j := by
  classical
  rw [form, Matrix.toBilin'_apply]
  simp only [Pi.single_apply, mul_ite, mul_zero, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [Matrix.of_apply]
  calc
    (∑ i, x i * (if i = j then 0 else 1)) =
        ∑ i, (x i + if i = j then x j else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = j
      · subst i
        simp [CharTwo.add_self_eq_zero]
      · simp [hi]
    _ = (∑ i, x i) + x j := by rw [Finset.sum_add_distrib]; simp

/-- Evaluation on a coordinate vector detects the uniform form's constant radical. -/
theorem form_apply_basis (x : V n) (j : Fin n) :
    form n x (Pi.single j 1) = (∑ i, x i) + x j :=
  form_basis x j

private theorem radical_constant (x : (form n).ker) (i j : Fin n) : x.val i = x.val j := by
  have h (k : Fin n) : (∑ a, x.val a) + x.val k = 0 := by
    rw [←form_basis]
    have hz := congrArg (fun f : Module.Dual (ZMod 2) (V n) => f (Pi.single k 1)) x.property
    exact hz
  have hi := h i
  have hj := h j
  exact add_left_cancel (hi.trans hj.symm)

private theorem radical_finrank_le (hn : 0 < n) : finrank (ZMod 2) (form n).ker ≤ 1 := by
  let j : Fin n := ⟨0,hn⟩
  let f : (form n).ker →ₗ[ZMod 2] ZMod 2 :=
    (LinearMap.proj j).comp (form n).ker.subtype
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    exact (radical_constant x i j).trans (hxy.trans (radical_constant y j i))
  simpa using LinearMap.finrank_le_finrank_of_injective hf

/-- A totally isotropic subspace for the uniform nonzero off-diagonal form
has codimension at least half the degree minus one. This will be applied to
the original conjugate-plane orbit and the elementary G.2.3 intersection. -/
theorem isotropic_codimension_bound (E : Submodule (ZMod 2) (V n))
    (hE : ∀ x ∈ E, ∀ y ∈ E, form n x y = 0)
    (m : ℕ) (hcodim : n ≤ finrank (ZMod 2) E + m) : n ≤ 2 * m + 1 := by
  by_cases hn : n = 0
  · omega
  have hle : E ≤ (form n).orthogonal E := by
    intro y hy x hx
    exact hE x hx y hy
  have hd := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := form n) E
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_mono (inf_le_right : E ⊓ (form n).ker ≤ (form n).ker)
  have h3 := radical_finrank_le (Nat.pos_of_ne_zero hn)
  have hdim : finrank (ZMod 2) (V n) = n := by simp [V]
  rw [hdim] at hd
  omega
/-- The orbit map need not be injective. Its preimage of the original
isotropic subgroup has no larger codimension than that subgroup. -/
theorem orbit_degree_bound {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (B : LinearMap.BilinForm (ZMod 2) W) (f : V n →ₗ[ZMod 2] W)
    (hf : ∀ x y, form n x y = B (f x) (f y))
    (E : Submodule (ZMod 2) W) (hE : ∀ x ∈ E, ∀ y ∈ E, B x y = 0)
    (m : ℕ) (hm : finrank (ZMod 2) (W ⧸ E) ≤ m) : n ≤ 2 * m + 1 := by
  let g := E.mkQ.comp f
  have hk : LinearMap.ker g = E.comap f := by
    ext x
    simp [g]
  have hd := g.finrank_range_add_finrank_ker
  have hr : finrank (ZMod 2) g.range ≤ finrank (ZMod 2) (W ⧸ E) :=
    Submodule.finrank_le _
  have hn : finrank (ZMod 2) (V n) = n := by simp [V]
  rw [hk, hn] at hd
  apply isotropic_codimension_bound (E.comap f) ?_ m (by omega)
  intro x hx y hy
  rw [hf]
  exact hE (f x) hx (f y) hy

/-- A spanning orbit whose distinct ordered pairs all have the same
pairing realizes the uniform form whenever the ambient polar form is nonzero. -/
theorem pullback_eq_uniform {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (B : LinearMap.BilinForm (ZMod 2) W) (hB : B.IsAlt) (hne : B ≠ 0)
    (f : V n →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (hp : ∀ i j i' j' : Fin n, i ≠ j → i' ≠ j' →
      B (f (Pi.single i 1)) (f (Pi.single j 1)) =
      B (f (Pi.single i' 1)) (f (Pi.single j' 1))) :
    B.comp f f = form n := by
  classical
  have hnf : B.comp f f ≠ 0 := by
    intro hz
    apply hne
    ext x y
    obtain ⟨a,rfl⟩ := hf x
    obtain ⟨b,rfl⟩ := hf y
    exact congrArg (fun C : LinearMap.BilinForm (ZMod 2) (V n) => C a b) hz
  obtain ⟨a,b,hab⟩ : ∃ a b : Fin n,
      B (f (Pi.single a 1)) (f (Pi.single b 1)) ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hnf
    apply LinearMap.BilinForm.ext_basis (Pi.basisFun (ZMod 2) (Fin n))
    intro i j
    simpa only [Pi.basisFun_apply, LinearMap.BilinForm.comp_apply, LinearMap.zero_apply] using hc i j
  have hab' : a ≠ b := by
    intro he
    subst b
    exact hab (hB _)
  have hone : B (f (Pi.single a 1)) (f (Pi.single b 1)) = 1 := by
    have binary : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    exact (binary _).resolve_left hab
  apply LinearMap.BilinForm.ext_basis (Pi.basisFun (ZMod 2) (Fin n))
  intro i j
  simp only [Pi.basisFun_apply, LinearMap.BilinForm.comp_apply]
  change B (f (Pi.single i 1)) (f (Pi.single j 1)) =
    form n (Pi.single i 1) (Pi.single j 1)
  rw [form, Matrix.toBilin'_single]
  by_cases hij : i = j
  · subst j
    simpa using hB (f (Pi.single i 1))
  · simpa [hij] using (hp i j a b hij hab').trans hone

/-- The nonzero invariant polar form bounds a doubly transitive generating
orbit using the actual isotropic subgroup supplied by G.2.3. -/
theorem invariant_orbit_degree_bound {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (B : LinearMap.BilinForm (ZMod 2) W) (hB : B.IsAlt) (hne : B ≠ 0)
    (f : V n →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (hp : ∀ i j i' j' : Fin n, i ≠ j → i' ≠ j' →
      B (f (Pi.single i 1)) (f (Pi.single j 1)) =
      B (f (Pi.single i' 1)) (f (Pi.single j' 1)))
    (E : Submodule (ZMod 2) W) (hE : ∀ x ∈ E, ∀ y ∈ E, B x y = 0)
    (m : ℕ) (hm : finrank (ZMod 2) (W ⧸ E) ≤ m) : n ≤ 2*m+1 := by
  apply orbit_degree_bound B f ?_ E hE m hm
  intro x y
  exact (congrArg (fun C : LinearMap.BilinForm (ZMod 2) (V n) => C x y)
    (pullback_eq_uniform B hB hne f hf hp)).symm

private theorem exponential_growth (f : ℕ) (hf : 4 ≤ f) :
    2 * (f + 1) < 2 ^ f := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hf
  induction k with
  | zero => decide
  | succ k ih =>
    have hp : 2 ≤ 2 ^ (4+k) := by
      calc
        2 = 2 ^ 1 := by decide
        _ ≤ 2 ^ (4+k) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [show 4 + (k + 1) = (4+k)+1 by omega, pow_succ]
    omega

/-- With elementary actor rank at most f+1, the binary projective orbit
has degree at most nine. -/
theorem linear_field_degree (f : ℕ) (hf : 1 < f)
    (hb : 2 ^ f + 1 ≤ 2 * (f + 1) + 1) : f = 2 ∨ f = 3 := by
  by_contra hc
  have hf4 : 4 ≤ f := by omega
  have hg := exponential_growth f hf4
  omega
end UniformBinaryPolar
