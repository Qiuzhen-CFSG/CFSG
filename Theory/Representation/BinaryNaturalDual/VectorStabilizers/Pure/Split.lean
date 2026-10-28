module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Structure
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Modules
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# A genuine semidirect-product model of the pure stabilizer

A covector paired to x chooses a complement to its line and hence a
homomorphic section of the quotient action. Conjugation by that section
is the action on the actual elementary radical. Multiplication gives the
semidirect-product equivalence, with inverse g ↦ (g s(π(g))⁻¹, π(g)).

Source: Aschbacher–Smith, H.9.1(3), printed pp.389–390.
-/

public section
namespace BinaryNaturalDual.VectorStabilizers.Pure
open BinaryLinear BinaryLinear.OuterCyclic

private def sectionAction {G H : Type*} [Group G] [Group H]
    (π : G →* H) (s : H →* G) : H →* MulAut π.ker :=
  (MulAut.conjNormal : G →* MulAut π.ker).comp s

private def sectionEquiv {G H : Type*} [Group G] [Group H]
    (π : G →* H) (s : H →* G) (hs : Function.RightInverse s π) :
    SemidirectProduct π.ker H (sectionAction π s) ≃* G where
  toFun z := z.left.val * s z.right
  invFun g := ⟨⟨g * (s (π g))⁻¹, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hs, mul_inv_cancel]⟩, π g⟩
  left_inv z := by
    apply SemidirectProduct.ext
    · apply Subtype.ext
      change z.left.val * s z.right * (s (π (z.left.val * s z.right)))⁻¹ = z.left.val
      rw [map_mul, (MonoidHom.mem_ker.mp z.left.property), hs, one_mul, mul_inv_cancel_right]
    · change π (z.left.val * s z.right) = z.right
      rw [map_mul, (MonoidHom.mem_ker.mp z.left.property), hs, one_mul]
  right_inv g := by
    change g * (s (π g))⁻¹ * s (π g) = g
    exact inv_mul_cancel_right _ _
  map_mul' a b := by
    change a.left.val * (s a.right * b.left.val * (s a.right)⁻¹) * s (a.right * b.right) = _
    rw [map_mul]
    group

/-- A choice of complement gives an actual section, with no extra existence premise. -/
noncomputable def splitSection {n : ℕ} (d : CoordinateAction n)
    {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    BinaryLinear.GL (pointQuotient x) →* innerStabilizer d (x,0) :=
  innerQuotientSection d (Classical.choose_spec (exists_pairing hx))

theorem splitSection_rightInverse {n : ℕ} (d : CoordinateAction n)
    {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    Function.RightInverse (splitSection d hx) (innerQuotientAction d x) :=
  innerQuotientSection_rightInverse d (Classical.choose_spec (exists_pairing hx))

/-- The quotient acts on the actual radical by conjugation through its section. -/
noncomputable def splitAction {n : ℕ} (d : CoordinateAction n)
    {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    BinaryLinear.GL (pointQuotient x) →* MulAut (innerRadical d x) :=
  sectionAction (innerQuotientAction d x) (splitSection d hx)

/-- A genuine split extension of the actual radical by the marked quotient linear group. -/
noncomputable def innerSemidirectEquiv {n : ℕ} (d : CoordinateAction n)
    {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    SemidirectProduct (innerRadical d x) (BinaryLinear.GL (pointQuotient x)) (splitAction d hx) ≃*
      innerStabilizer d (x,0) :=
  sectionEquiv (innerQuotientAction d x) (splitSection d hx) (splitSection_rightInverse d hx)

@[simp] theorem innerSemidirectEquiv_apply {n : ℕ} (d : CoordinateAction n)
    {x : OuterCyclic.Space n} (hx : x ≠ 0)
    (z : SemidirectProduct (innerRadical d x) (BinaryLinear.GL (pointQuotient x)) (splitAction d hx)) :
    innerSemidirectEquiv d hx z = z.left.val * splitSection d hx z.right := by rfl

/-- The source full stabilizer has the same actual split extension. -/
noncomputable def fullSemidirectEquiv {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    SemidirectProduct (innerRadical d x) (BinaryLinear.GL (pointQuotient x)) (splitAction d hx) ≃*
      fullStabilizer d (x,0) :=
  (innerSemidirectEquiv d hx).trans
    (MulEquiv.subgroupCongr (pure_fullStabilizer_eq_innerStabilizer hn d hx).symm)

/-- The full stabilizer modulo its intrinsic two-core is GL_(n−1)(2). -/
noncomputable def fullQuotientTwoCoreEquivLinear {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    (fullStabilizer d (x,0) ⧸ pCore 2 (fullStabilizer d (x,0))) ≃* LinearGroup (n - 1) := by
  rw [pure_fullStabilizer_eq_innerStabilizer hn d hx]
  exact (QuotientGroup.quotientMulEquivOfEq (inner_twoCore d x)).trans
    (innerQuotientEquivLinear d hx)

end BinaryNaturalDual.VectorStabilizers.Pure
