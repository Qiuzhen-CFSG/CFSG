module

public import Theory.SpecificGroups.SymplecticFour.Binary.FieldTransport
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fintype.Perm

/-!
# The binary symplectic point stabilizer

The actual point parabolic in the four-dimensional matrix symplectic group
over `ZMod 2` is isomorphic to `S₂ × S₄`.

Use the alternating matrix `B` with every off-diagonal entry equal to one.
Coordinate permutations preserve `B` and fix the all-ones vector `c`.
The central involution `x ↦ x + (∑ i, x i) • c` complements each column of a
permutation matrix. These two operations give the product homomorphism.

For exhaustion, preservation of `B` and fixation of `c` make every column
have odd weight, hence it is a coordinate vector or its complement.
Pairing with a third column rules out repeated coordinate indices; the form
then forces all four complement choices to agree. Thus these are all the
matrices in the stabilizer. An explicit change of basis has Gram matrix `J`
and takes the standard point vector to `c`, identifying this stabilizer with
the subgroup defined in `Flag`. All finite coordinate checks use Lean's kernel.

This constructs the point-parabolic model underlying the binary case of
Aschbacher--Smith, *The Classification of Quasithin Groups*, F.1.12(I)(2),
printed pp.262--264. The source's `LᵢS` identifications are separate bridges.
-/

open Matrix

namespace Theory.SpecificGroups.SymplecticFour.Binary

private abbrev V := Fin 4 → ZMod 2
private abbrev M := Matrix (Fin 4) (Fin 4) (ZMod 2)
private abbrev I := Fin 2 ⊕ Fin 2
private abbrev Product := Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4)
private def c : V := fun _ => 1
private def B : M := fun i j => if i = j then 0 else 1
private def w (a : ZMod 2) (i : Fin 4) : V := fun j => (if j = i then 1 else 0) + a
private def bit (p : Equiv.Perm (Fin 2)) : ZMod 2 := (p 0).val
private def model (p : Product) : M := fun i j => w (bit p.1) (p.2 j) i
set_option maxRecDepth 100000

private theorem odd_vec : ∀ x : V, (∑ i, x i) = 1 → ∃ a i, x = w a i := by decide +kernel

private theorem parameters : ∀ a : Fin 4 → ZMod 2, ∀ s : Fin 4 → Fin 4,
    (∀ i j, (if s i = s j then 0 else 1) + a i + a j = (if i = j then 0 else 1)) →
    (∀ i, a i = a 0) ∧ Function.Bijective s := by
  intro a s h
  have hinj : Function.Injective s := by
    intro i j hij
    by_contra hne
    obtain ⟨k, hik, hjk⟩ :=
      (show ∀ i j : Fin 4, ∃ k : Fin 4, i ≠ k ∧ j ≠ k by decide) i j
    have hai : a i = a j := by
      have hi := h i k
      have hj := h j k
      rw [if_neg hik, hij] at hi
      rw [if_neg hjk] at hj
      exact add_left_cancel (add_right_cancel (hi.trans hj.symm))
    have hh := h i j
    rw [if_pos hij, if_neg hne, zero_add, hai] at hh
    have hz : ∀ x : ZMod 2, x + x = 0 := by decide
    rw [hz] at hh
    exact zero_ne_one hh
  refine ⟨?_, hinj.bijective_of_finite⟩
  intro i
  by_cases hi : i = 0
  · rw [hi]
  · have hh := h i 0
    rw [if_neg (fun hs => hi (hinj hs)), if_neg hi] at hh
    exact (show ∀ x y : ZMod 2, 1 + x + y = 1 → x = y by decide) _ _ hh

private theorem w_pair : ∀ a b : ZMod 2, ∀ i j : Fin 4,
    B.toBilin' (w a i) (w b j) = (if i = j then 0 else 1) + a + b := by decide +kernel

private theorem c_pair : ∀ x : V, B.toBilin' c x = ∑ i, x i := by decide +kernel

private theorem basis_pair : ∀ i j : Fin 4,
    B.toBilin' (Pi.single i 1) (Pi.single j 1) = (if i = j then 0 else 1) := by decide +kernel

private theorem c_basis : ∀ j : Fin 4, B.toBilin' c (Pi.single j 1) = 1 := by decide +kernel

private theorem w_inj : ∀ a b : ZMod 2, ∀ i j : Fin 4, w a i = w b j → a = b ∧ i = j := by decide +kernel

private theorem bit_bij : Function.Bijective bit := by decide +kernel

private theorem model_form : ∀ p : Product, (model p)ᵀ * B * model p = B := by decide +kernel

private theorem model_c : ∀ p : Product, model p *ᵥ c = c := by decide +kernel

private theorem model_one : model 1 = 1 := by decide +kernel

private theorem bit_mul : ∀ p q : Equiv.Perm (Fin 2), bit (p * q) = bit p + bit q := by
  decide +kernel

private theorem model_mul (p q : Product) : model (p * q) = model p * model q := by
  ext i j
  simp [model, w, Matrix.mul_apply, add_mul, mul_add, Finset.sum_add_distrib,
    ← p.2.symm_apply_eq, bit_mul, add_comm, add_left_comm, add_assoc]
  exact Or.inl (by decide)

private theorem preserves {A : M} (hA : Aᵀ * B * A = B) (x y : V) :
    B.toBilin' (A *ᵥ x) (A *ᵥ y) = B.toBilin' x y := by
  have h := Matrix.toBilin'_comp B A A
  rw [hA] at h
  exact congrArg (fun f : LinearMap.BilinForm (ZMod 2) V => f x y) h

private theorem classify (A : M) (hA : Aᵀ * B * A = B) (hc : A *ᵥ c = c) :
    ∃ p : Product, A = model p := by
  have hcol (j : Fin 4) : ∃ a i, A.col j = w a i := by
    apply odd_vec
    have h := preserves hA c (Pi.single j 1)
    rw [hc, c_basis, c_pair] at h
    simpa [Matrix.mulVec_single] using h
  choose a s hs using hcol
  have hp := parameters a s (by
    intro i j
    have h := preserves hA (Pi.single i 1) (Pi.single j 1)
    simpa [Matrix.mulVec_single, hs, w_pair, basis_pair, B] using h)
  obtain ⟨t, ht⟩ := bit_bij.surjective (a 0)
  refine ⟨(t, Equiv.ofBijective s hp.2), ?_⟩
  ext i j
  exact (congrFun (hs j) i).trans (by simp [model, ht, hp.1 j])

private theorem model_injective : Function.Injective model := by
  intro p q h
  have hw (j : Fin 4) : w (bit p.1) (p.2 j) = w (bit q.1) (q.2 j) :=
    funext fun i => congrFun (congrFun h i) j
  apply Prod.ext
  · exact bit_bij.injective (w_inj _ _ _ _ (hw 0)).1
  · exact Equiv.ext fun j => (w_inj _ _ _ _ (hw j)).2

-- Columns c, (0,1,1,0), (1,0,0,0), (0,1,0,1).

private def C : Matrix (Fin 4) I (ZMod 2) := fun i j =>
  Sum.elim (![![1, 1, 1, 1], ![0, 1, 1, 0]]) (![![1, 0, 0, 0], ![0, 1, 0, 1]]) j i

private def D : Matrix I (Fin 4) (ZMod 2) :=
  Sum.elim (![![0, 1, 1, 1], ![0, 1, 0, 1]]) (![![1, 1, 1, 1], ![0, 1, 1, 0]])

private theorem CD : C * D = 1 := by decide +kernel

private theorem DC : D * C = 1 := by decide +kernel

private theorem gram : Cᵀ * B * C = Matrix.J (Fin 2) (ZMod 2) := by decide +kernel

private theorem inv_gram : Dᵀ * Matrix.J (Fin 2) (ZMod 2) * D = B := by decide +kernel

private theorem Ce : C *ᵥ e (F := ZMod 2) 0 = c := by decide +kernel

private theorem Dc : D *ᵥ c = e (F := ZMod 2) 0 := by decide +kernel

private def conjugate (A : M) : Matrix I I (ZMod 2) := D * A * C

private theorem conjugate_one : conjugate 1 = 1 := by simp [conjugate, DC]

private theorem conjugate_mul (A A' : M) : conjugate (A * A') = conjugate A * conjugate A' := by
  simp only [conjugate]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc C D, CD, Matrix.one_mul]

private theorem conjugate_form {A : M} (h : Aᵀ * B * A = B) :
    (conjugate A)ᵀ * Matrix.J (Fin 2) (ZMod 2) * conjugate A = Matrix.J (Fin 2) (ZMod 2) := by
  simp only [conjugate, Matrix.transpose_mul]
  calc
    _ = Cᵀ * (Aᵀ * (Dᵀ * Matrix.J (Fin 2) (ZMod 2) * D) * A) * C := by simp only [Matrix.mul_assoc]
    _ = Matrix.J (Fin 2) (ZMod 2) := by rw [inv_gram, h, gram]

private theorem conjugate_c {A : M} (h : A *ᵥ c = c) :
    conjugate A *ᵥ e (F := ZMod 2) 0 = e 0 := by
  simp only [conjugate, ← Matrix.mulVec_mulVec, Ce, h, Dc]

private theorem conjugate_injective : Function.Injective conjugate := by
  intro A A' h
  have h' := congrArg (fun X => C * X * D) h
  simpa only [conjugate, Matrix.mul_assoc, ← Matrix.mul_assoc C D, CD,
    Matrix.one_mul, Matrix.mul_one] using h'

private def embedding : Product →* pointParabolic (F := ZMod 2) where
  toFun p := ⟨⟨conjugate (model p), SymplecticGroup.mem_iff'.mpr
    (conjugate_form (model_form p))⟩, by
      apply (mem_pointParabolic_iff _).mpr
      have h : (conjugate (model p)).col (.inl 0) = e (F := ZMod 2) 0 := by
        simpa [e, Matrix.mulVec_single] using conjugate_c (model_c p)
      constructor
      · exact congrFun h (.inl 1)
      · intro i
        exact congrFun h (.inr i)⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    change conjugate (model 1) = 1
    rw [model_one, conjugate_one]
  map_mul' p q := by
    apply Subtype.ext
    apply Subtype.ext
    exact (congrArg conjugate (model_mul p q)).trans (conjugate_mul _ _)

private theorem embedding_injective : Function.Injective embedding := by
  intro p q h
  exact model_injective (conjugate_injective
    (congrArg (fun g : pointParabolic (F := ZMod 2) => g.val.val) h))

private theorem point_fixed (g : pointParabolic (F := ZMod 2)) :
    g.val.val *ᵥ e (F := ZMod 2) 0 = e 0 := by
  have hshape : ∀ x : Vector (ZMod 2), x ≠ 0 →
      x (.inl 1) = 0 → (∀ i, x (.inr i) = 0) → x = e 0 := by decide +kernel
  apply hshape
  · intro hz
    have hz' : toLinear g.val (e 0) = toLinear g.val 0 := by
      simpa [smul_eq_mulVec] using hz
    have he := (toLinear g.val).injective hz'
    exact (by decide : e (F := ZMod 2) 0 ≠ 0) he
  · simpa [e, Matrix.mulVec_single] using ((mem_pointParabolic_iff _).mp g.property).1
  · intro i
    simpa [e, Matrix.mulVec_single] using ((mem_pointParabolic_iff _).mp g.property).2 i

private theorem embedding_surjective : Function.Surjective embedding := by
  intro g
  let A : M := C * g.val.val * D
  have hA : Aᵀ * B * A = B := by
    dsimp [A]
    rw [Matrix.transpose_mul, Matrix.transpose_mul]
    calc
      _ = Dᵀ * (g.val.valᵀ * (Cᵀ * B * C) * g.val.val) * D := by
        simp only [Matrix.mul_assoc]
      _ = B := by rw [gram, SymplecticGroup.mem_iff'.mp g.val.property, inv_gram]
  have hc : A *ᵥ c = c := by
    simp only [A, ← Matrix.mulVec_mulVec, Dc, point_fixed g, Ce]
  obtain ⟨p, hp⟩ := classify A hA hc
  refine ⟨p, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change conjugate (model p) = g.val.val
  rw [← hp]
  simp only [conjugate, A, Matrix.mul_assoc, ← Matrix.mul_assoc D C, DC,
    Matrix.one_mul, Matrix.mul_one]

/-- The concrete binary point parabolic is the product of the symmetric groups
on two and four letters. The inverse is induced by permutation matrices and
the central column-complement involution, in the displayed symplectic basis. -/
public noncomputable def pointParabolicZModEquivProd :
    pointParabolic (F := ZMod 2) ≃* (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4)) :=
  (MulEquiv.ofBijective embedding ⟨embedding_injective, embedding_surjective⟩).symm

end Theory.SpecificGroups.SymplecticFour.Binary
