module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus
public import Theory.Representation.OrthogonalFourMinusHermitianEquiv.Transport
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.Algebra.CharP.Two

/-!
# The abelian derived isometry group of a binary plane

For Q(x,y) = x² + xy - ay² in characteristic two, use the bilinear form
B(v,w) = v₁w₁ + v₁w₂ - av₂w₂. An isometry changes B by a scalar multiple
of the polar form. This scalar defines a homomorphism to the additive field.
Its kernel commutes with the operator J(x,y) = (-ay,x+y), and every map
in that kernel is a polynomial of degree at most one in J. Thus the kernel,
and hence the commutator subgroup of the actual isometry group, is abelian.

This direct calculation does not need anisotropy or finiteness. Deleting the
empty hyperbolic coordinates then identifies the literal minus-rank-zero and
minus-rank-one quadratic spaces with the chosen anisotropic plane. Their
actual commutator/scalar quotients inherit commutativity.

Source application: the low-rank boundary of Aschbacher–Smith Hypothesis
13.3.1(2), printed p.884; the minus carriers follow GLS3 §2.7. The bilinear
calculation supplies the degenerate cases without an orthogonal classification.
-/

public section
open scoped IsMulCommutative
open Theory.AlgebraicGroup
namespace ClassicalOrthogonal.Minus.SourcePredicatePlane

variable {F : Type*} [Field F] [CharP F 2] (a : F)
private abbrev O := Orthogonal F (F × F) (plane F a)
-- A bilinear form whose diagonal is the quadratic form.
private def B (v w : F × F) : F := v.1 * w.1 + v.1 * w.2 - a * v.2 * w.2
private def P (v w : F × F) : F := v.1 * w.2 + v.2 * w.1

omit [CharP F 2] in
private theorem preserve (g : O a) (v : F × F) : plane F a (g.val v) = plane F a v :=
  (mem_quadraticIsometrySubgroup _ _).mp g.property v

private theorem polar_preserve (g : O a) (v w : F × F) : P (g.val v) (g.val w) = P v w := by
  have h : (plane F a).polarBilin (g.val v) (g.val w) = (plane F a).polarBilin v w := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      ← map_add, preserve]
  simpa only [plane_polar, zero_mul, zero_add, sub_zero, CharTwo.two_eq_zero, P] using h

omit [CharP F 2] in
private theorem coords (g : O a) (v : F × F) :
    g.val v = v.1 • g.val (1, 0) + v.2 • g.val (0, 1) := by
  rw [← map_smul, ← map_smul, ← map_add]
  congr 1
  ext <;> simp

private def shift (g : O a) : F := B a (g.val (1, 0)) (g.val (0, 1)) - 1

private theorem B_shift (g : O a) (v w : F × F) :
    B a (g.val v) (g.val w) = B a v w + shift a g * P v w := by
  have h1 := preserve a g (1, 0)
  have h2 := preserve a g (0, 1)
  have h3 := polar_preserve a g (1, 0) (0, 1)
  simp only [plane_apply, mul_zero, zero_pow (by decide : 2 ≠ 0),
    mul_one, one_pow, add_zero, sub_zero] at h1 h2
  simp only [P, mul_zero, mul_one, add_zero] at h3
  rw [coords a g v, coords a g w]
  simp only [B, shift, P, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  linear_combination (norm := ring_nf) v.1 * w.1 * h1 + v.2 * w.2 * h2 + v.2 * w.1 * h3
  simp [CharTwo.two_eq_zero]

-- The difference of the transported bilinear form is a scalar multiple of
-- the alternating polar form. Its scalar is additive under composition.
private def character : O a →* Multiplicative F where
  toFun g := Multiplicative.ofAdd (shift a g)
  map_one' := by
    change shift a 1 = 0
    simp [shift, B]
  map_mul' g h := by
    change shift a (g * h) = shift a g + shift a h
    change B a (g.val (h.val (1, 0))) (g.val (h.val (0, 1))) - 1 = _
    rw [B_shift, polar_preserve]
    simp only [P, mul_one, mul_zero, add_zero]
    simp only [shift]
    ring

-- The operator representing B relative to the nonsingular polar form.
private def J (v : F × F) : F × F := (-a * v.2, v.1 + v.2)

omit [CharP F 2] in
private theorem B_eq (v w : F × F) : B a v w = P v (J a w) := by
  simp only [B, P, J]
  ring

omit [CharP F 2] in
private theorem P_separating {v w : F × F} (h : ∀ x, P x v = P x w) : v = w := by
  have h1 := h (1, 0)
  have h2 := h (0, 1)
  exact Prod.ext (by simpa [P] using h2) (by simpa [P] using h1)

private theorem commutes_J (g : O a) (hg : g ∈ (character a).ker) (w : F × F) :
    g.val (J a w) = J a (g.val w) := by
  have hg0 : shift a g = 0 := hg
  apply P_separating
  intro x
  obtain ⟨v, rfl⟩ := g.val.surjective x
  rw [polar_preserve, ← B_eq, ← B_eq, B_shift, hg0, zero_mul, add_zero]

-- Every map in the kernel is a polynomial of degree at most one in J.
private theorem kernel_coordinates (g : O a) (hg : g ∈ (character a).ker) (v : F × F) :
    g.val v = (v.1 * (g.val (1, 0)).1 - a * v.2 * (g.val (1, 0)).2,
      v.1 * (g.val (1, 0)).2 + v.2 * ((g.val (1, 0)).1 + (g.val (1, 0)).2)) := by
  have he := commutes_J a g hg (1, 0)
  simp only [J, mul_zero, neg_mul, add_zero] at he
  rw [coords a g v, he]
  ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  all_goals ring

private theorem kernel_commutative : IsMulCommutative (character a).ker := by
  apply IsMulCommutative.of_comm
  intro g h
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change g.val.val (h.val.val v) = h.val.val (g.val.val v)
  conv_lhs => rw [kernel_coordinates a g.val g.property]
  conv_rhs => rw [kernel_coordinates a h.val h.property]
  rw [kernel_coordinates a h.val h.property v, kernel_coordinates a g.val g.property v]
  ext <;> simp only <;> ring

/-- The derived isometry group of the binary plane is abelian. In particular,
this holds for the chosen anisotropic plane defining the minus family. -/
theorem plane_commutator_commutative : IsMulCommutative (Omega F (F × F) (plane F a)) := by
  let := kernel_commutative a
  apply IsMulCommutative.of_comm
  intro g h
  have hg := Abelianization.commutator_subset_ker (character a) g.property
  have hh := Abelianization.commutator_subset_ker (character a) h.property
  have he := mul_comm (⟨g.val, hg⟩ : (character a).ker) ⟨h.val, hh⟩
  exact Subtype.ext (congrArg (fun k : (character a).ker => k.val) he)

private noncomputable def dropZeroHyperbolic :
    (form F 0 a).IsometryEquiv (plane F a) where
  toFun := Prod.snd
  invFun v := (0, v)
  left_inv v := Prod.ext (Subsingleton.elim _ _) rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_app' v := by simp

private theorem omega_zero_commutative : IsMulCommutative (Omega F (Space F 0) (form F 0 a)) := by
  let e := Representation.OrthogonalFourMinus.HermitianEquiv.omegaCongr (dropZeroHyperbolic a)
  let := plane_commutator_commutative a
  apply IsMulCommutative.of_comm
  intro x y
  apply e.injective
  exact (map_mul e x y).trans ((mul_comm (e x) (e y)).trans (map_mul e y x).symm)

/-- Both truncated minus ranks use this plane, and their actual projective
Omega quotients are abelian. -/
theorem pOmegaMinus_commutative_of_le_one (F : Type*) [Field F] [Finite F] [CharP F 2]
    (r : ℕ) (hr : r ≤ 1) : IsMulCommutative (ClassicalGroup.POmegaMinus r F) := by
  have hr0 : r - 1 = 0 := Nat.sub_eq_zero_of_le hr
  have hc : IsMulCommutative (Omega F (Space F (r - 1)) (quadraticForm F r)) := by
    unfold quadraticForm
    rw [hr0]
    exact omega_zero_commutative (parameter F)
  let := hc
  infer_instance

end ClassicalOrthogonal.Minus.SourcePredicatePlane
