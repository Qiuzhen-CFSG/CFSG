module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Embedding
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.RankTwoCubic.Ternary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Cubics in every minus Omega and the smallest centralizer block

Completing the square in `u² + uv - a v²` splits the four-dimensional
minus space into the ternary form `xy + z²` and a line. The full ternary
isometry group extends faithfully by the identity on that line. The companion
module places the ternary elementary carrier in its full commutator subgroup;
functoriality of commutators then gives its faithful embedding in the literal
minus Omega. Transporting the known ternary cubic proves the rank-two case,
including over F₃. The published higher-rank construction gives all ranks
at least two.

Finally `coverBlockHom 1 hq` and the square-one scalar-kernel theorem give
an elementary subgroup of order nine in the literal `projectiveBlockHom`
image inside `ClassicalGroup.POmegaMinus 4 F`. This discharges the smallest
complementary cubic and block-rank step of Aschbacher–Smith,
*The Classification of Quasithin Groups*, A.2.17, printed p.39.
The identification of that block image with the source residual is separate.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix Theory.AlgebraicGroup
namespace ClassicalOrthogonal.Fundamental.MinusCentralizer
variable {F : Type*} [Field F]
namespace RankTwoCubic

/-- Complete the square in the final plane while retaining the hyperbolic pair. -/
def squareCoordinates : Minus.Space F 1 ≃ₗ[F] VectorB 1 F × F where
  toFun x := ((Sum.elim (fun i => (x.1 i).1) (fun i => (x.1 i).2),
    x.2.1 + x.2.2 / 2), x.2.2)
  invFun y := (fun i => (y.1.1 (.inl i), y.1.1 (.inr i)), (y.1.2 - y.2 / 2, y.2))
  left_inv x := by simp
  right_inv y := by
    apply Prod.ext
    · apply Prod.ext
      · funext i; cases i <;> rfl
      · simp
    · rfl
  map_add' x y := by
    apply Prod.ext
    · apply Prod.ext
      · funext i; cases i <;> rfl
      · simp [add_div]; ring
    · rfl
  map_smul' c x := by
    apply Prod.ext
    · apply Prod.ext
      · funext i; cases i <;> rfl
      · simp [smul_eq_mul]; ring
    · rfl

/-- The four-space splits orthogonally as `xy + z²` and a remaining line. -/
theorem squareCoordinates_form (h2 : (2 : F) ≠ 0) (a : F) (x : Minus.Space F 1) :
    Minus.form F 1 a x = formB 1 F (squareCoordinates x).1 -
      (a + (2 : F)⁻¹ ^ 2) * (squareCoordinates x).2 ^ 2 := by
  simp [Minus.form_apply, Minus.plane_apply, squareCoordinates, formB_apply, formD_apply]
  field_simp [h2]
  ring

/-- Extend every full ternary isometry by the identity on the remaining line. -/
def ternaryExtension (h2 : (2 : F) ≠ 0) (a : F) :
    quadraticIsometrySubgroup (formB 1 F) →*
      Minus.Orthogonal F (Minus.Space F 1) (Minus.form F 1 a) where
  toFun g := ⟨squareCoordinates.trans
    ((LinearEquiv.prodCongr g.val (LinearEquiv.refl F F)).trans squareCoordinates.symm),
    (mem_quadraticIsometrySubgroup _ _).mpr (by
      intro x
      rw [squareCoordinates_form h2, squareCoordinates_form h2]
      change formB 1 F (squareCoordinates (squareCoordinates.symm
          (g.val (squareCoordinates x).1, (squareCoordinates x).2))).1 -
        (a + (2 : F)⁻¹ ^ 2) * (squareCoordinates (squareCoordinates.symm
          (g.val (squareCoordinates x).1, (squareCoordinates x).2))).2 ^ 2 = _
      rw [LinearEquiv.apply_symm_apply,
        (mem_quadraticIsometrySubgroup _ _).mp g.property])⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact squareCoordinates.symm_apply_apply x
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change squareCoordinates.symm
      (g.val (h.val (squareCoordinates x).1), (squareCoordinates x).2) =
      squareCoordinates.symm
      (g.val (squareCoordinates (squareCoordinates.symm
        (h.val (squareCoordinates x).1, (squareCoordinates x).2))).1,
        (squareCoordinates (squareCoordinates.symm
        (h.val (squareCoordinates x).1, (squareCoordinates x).2))).2)
    rw [LinearEquiv.apply_symm_apply]

/-- In the completed-square coordinates, the extra line is fixed pointwise. -/
theorem ternaryExtension_coordinates (h2 : (2 : F) ≠ 0) (a : F)
    (g : quadraticIsometrySubgroup (formB 1 F)) (x : Minus.Space F 1) :
    squareCoordinates ((ternaryExtension h2 a g).val x) =
      (g.val (squareCoordinates x).1, (squareCoordinates x).2) :=
  squareCoordinates.apply_symm_apply _

/-- Extension by the identity preserves the entire ternary action faithfully. -/
theorem ternaryExtension_injective (h2 : (2 : F) ≠ 0) (a : F) :
    Function.Injective (ternaryExtension h2 a) := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hh := congrArg (fun k : Minus.Orthogonal F (Minus.Space F 1) (Minus.form F 1 a) =>
    (squareCoordinates (k.val (squareCoordinates.symm (v, 0)))).1) he
  simpa only [ternaryExtension_coordinates, LinearEquiv.apply_symm_apply] using hh


/-- The elementary ternary action extends into the literal full commutator carrier. -/
def ternaryOmegaHom (h2 : (2 : F) ≠ 0) (a : F) :
    OmegaOdd 1 F →* Minus.Omega F (Minus.Space F 1) (Minus.form F 1 a) :=
  (derivedMap (ternaryExtension h2 a)).comp (ternaryElementaryDerived h2)

theorem ternaryOmegaHom_injective (h2 : (2 : F) ≠ 0) (a : F) :
    Function.Injective (ternaryOmegaHom h2 a) := by
  intro x y h
  apply ternaryElementaryDerived_injective h2
  apply Subtype.ext
  exact ternaryExtension_injective h2 a (congrArg Subtype.val h)

/-- The four-dimensional form with any plane parameter contains a cubic in its
full orthogonal commutator group, whenever two is nonzero. -/
theorem rankTwoForm_exists_cubic (h2 : (2 : F) ≠ 0) (a : F) :
    ∃ b : Minus.Omega F (Minus.Space F 1) (Minus.form F 1 a), orderOf b = 3 := by
  obtain ⟨b, hb⟩ := oddRankOne_exists_cubic (F := F)
  exact ⟨ternaryOmegaHom h2 a b,
    (orderOf_injective _ (ternaryOmegaHom_injective h2 a) b).trans hb⟩

end RankTwoCubic

private theorem two_ne_zero_of_odd {p : ℕ} [CharP F p] (ho : Odd p) : (2 : F) ≠ 0 := by
  apply Ring.two_ne_zero
  rw [ringChar.eq F p]
  obtain ⟨k, hk⟩ := ho
  omega

/-- A cubic in the actual four-dimensional minus Omega, including over F₃. -/
theorem rankTwoMinus_exists_cubic [Finite F] {p : ℕ} [CharP F p] (ho : Odd p) :
    ∃ b : Minus.Omega F (Minus.Space F 1) (Minus.quadraticForm F 2), orderOf b = 3 :=
  RankTwoCubic.rankTwoForm_exists_cubic (two_ne_zero_of_odd ho) (Minus.parameter F)

/-- Every minus rank at least two has a cubic in its full commutator carrier. -/
theorem minus_exists_cubic [Finite F] {p : ℕ} [CharP F p]
    (hp : p.Prime) (ho : Odd p) (m : ℕ) (hm : 2 ≤ m) :
    ∃ b : Minus.Omega F (Minus.Space F (m - 1)) (Minus.quadraticForm F m),
      orderOf b = 3 := by
  by_cases h : m = 2
  · subst m
    exact rankTwoMinus_exists_cubic ho
  · have he : m = (m - 3) + 3 := by omega
    rw [he]
    exact higherMinus_exists_cubic _ (field_card_gt_two hp ho)

/-- The smallest source block, inside PΩ⁻₈, already has an elementary subgroup
of order nine in the literal projective block image. -/
theorem smallestBlock_contains_nine [Finite F] {p : ℕ} [CharP F p]
    (ho : Odd p) (hq : 2 < Nat.card F) :
    ∃ E : Subgroup (ClassicalGroup.POmegaMinus 4 F),
      E ≤ (projectiveBlockHom 1 hq).range ∧
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨b, hb⟩ := rankTwoMinus_exists_cubic (F := F) ho
  exact omegaProjective_contains_nine (Minus.quadraticForm F 4)
    ⟨(0, (1, 0)), by simp [Minus.quadraticForm, Minus.plane_apply]⟩
    (coverBlockHom 1 hq) (coverBlockHom_injective _ _) b hb

end ClassicalOrthogonal.Fundamental.MinusCentralizer
