module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Tactic

/-!
# Binary tensor coordinates and involution ranks

Distributing `(F₂ × F₂) ⊗ W` gives `W × W`. In these coordinates, a
second-factor operator acts diagonally, and a swap in the first factor gives
`(x,y) ↦ (a y,a x)`. The former doubles displacement rank. When `a² = 1`,
the latter has fixed space isomorphic to `W`, hence displacement rank `dim W`.
The cubic operator `(x,y) ↦ (y,x+y)` has order dividing three, has no nonzero
fixed vector, and commutes with every diagonal operator. It therefore supplies
transitivity on any binary moved plane for which the displayed actors occur.

These calculations support Aschbacher–Smith, *The Classification of Quasithin
Groups*, G.11.2(9), printed p.364, and the proof of 6.2.19, printed p.691.
The explicit tensor equivalence and intertwining equations are proved here.
Identification of the S₃ actors and the two distinct four-dimensional modules,
and their rank-one involutions, remains the responsibility of the concrete
model calculation; it is not assumed by a family label.
-/

@[expose] public section

open scoped TensorProduct

namespace Representation.RankTwo.TensorCoordinates
variable {W G : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Group G]

private lemma binary_add_self (x : W) : x + x = 0 := by
  have h := @two_smul (ZMod 2) W _ _ _ x
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [htwo, zero_smul] at h
  exact h.symm

/-- The action confined to the second factor. -/
def diagonal (a : Module.End (ZMod 2) W) : Module.End (ZMod 2) (W × W) :=
  a.prodMap a

/-- The tensor of a coordinate swap with the second-factor operator. -/
def mixed (a : Module.End (ZMod 2) W) : Module.End (ZMod 2) (W × W) :=
  (a.comp (LinearMap.snd _ _ _)).prod (a.comp (LinearMap.fst _ _ _))

/-- The natural order-three binary operator, with coefficients in an arbitrary module. -/
def cubic : Module.End (ZMod 2) (W × W) :=
  (LinearMap.snd _ _ _).prod (LinearMap.fst _ _ _ + LinearMap.snd _ _ _)

/-- Displacement of a diagonal actor is the product of two displacement spaces. -/
def diagonalRangeEquiv (a : Module.End (ZMod 2) W) :
    (LinearMap.range (a - 1) × LinearMap.range (a - 1)) ≃ₗ[ZMod 2]
      LinearMap.range (diagonal a - 1) where
  toFun p := ⟨(p.1, p.2), by
    obtain ⟨u, hu⟩ := p.1.property
    obtain ⟨v, hv⟩ := p.2.property
    exact ⟨(u, v), Prod.ext hu hv⟩⟩
  invFun p := (⟨p.val.1, by
    obtain ⟨q, hq⟩ := p.property
    exact ⟨q.1, congrArg Prod.fst hq⟩⟩,
    ⟨p.val.2, by
      obtain ⟨q, hq⟩ := p.property
      exact ⟨q.2, congrArg Prod.snd hq⟩⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A second-factor actor has twice its original displacement rank. -/
lemma finrank_diagonal [FiniteDimensional (ZMod 2) W] (a : Module.End (ZMod 2) W) :
    Module.finrank (ZMod 2) (LinearMap.range (diagonal a - 1)) =
      2 * Module.finrank (ZMod 2) (LinearMap.range (a - 1)) := by
  have h := (diagonalRangeEquiv a).finrank_eq
  rw [Module.finrank_prod] at h
  omega

/-- Fixed vectors of a mixed involution are exactly `(a x,x)`. -/
def mixedFixedEquiv (a : Module.End (ZMod 2) W) (ha : a * a = 1) :
    W ≃ₗ[ZMod 2] LinearMap.ker (mixed a - 1) where
  toFun x := ⟨(a x, x), by
    change (a x, a (a x)) - (a x, x) = 0
    rw [show a (a x) = x from LinearMap.congr_fun ha x, sub_self]⟩
  invFun p := p.val.2
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · have h := congrArg Prod.fst p.property
      change a p.val.2 - p.val.1 = 0 at h
      exact sub_eq_zero.mp h
    · rfl
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

/-- A mixed involution displaces half the tensor space. -/
lemma finrank_mixed [FiniteDimensional (ZMod 2) W] (a : Module.End (ZMod 2) W)
    (ha : a * a = 1) :
    Module.finrank (ZMod 2) (LinearMap.range (mixed a - 1)) =
      Module.finrank (ZMod 2) W := by
  have he := (mixedFixedEquiv a ha).finrank_eq
  have h := (mixed a - 1).finrank_range_add_finrank_ker
  rw [Module.finrank_prod, ← he] at h
  omega

/-- The displayed cubic operator has period three. -/
lemma cubic_pow_three : (cubic (W := W)) ^ 3 = 1 := by
  ext p <;> simp [cubic, pow_succ, Module.End.mul_apply, binary_add_self]

/-- The displayed cubic operator fixes only zero. -/
lemma cubic_fixed_free (p : W × W) (hp : cubic p = p) : p = 0 := by
  have h1 : p.2 = p.1 := congrArg Prod.fst hp
  have h2 : p.1 + p.2 = p.2 := congrArg Prod.snd hp
  have h0 : p.1 = 0 := add_right_cancel (h2.trans (zero_add _).symm)
  exact Prod.ext h0 (h1.trans h0)

/-- The two tensor factors commute. -/
lemma cubic_commutes_diagonal (a : Module.End (ZMod 2) W) :
    cubic * diagonal a = diagonal a * cubic := by
  ext p <;> simp [cubic, diagonal, Module.End.mul_apply]

lemma stabilizerTransitive_of_coordinates
    (ρ : Representation (ZMod 2) G (W × W)) (hfaith : Function.Injective ρ)
    (v c : G) (a : Module.End (ZMod 2) W)
    (hv : ρ v = diagonal a) (hc : ρ c = cubic)
    [FiniteDimensional (ZMod 2) (movedSpace ρ v)]
    (hrank : Module.finrank (ZMod 2) (movedSpace ρ v) = 2) :
    StabilizerTransitive ρ (movedSpace ρ v) := by
  apply stabilizerTransitive_of_order_three ρ v c hrank
  · apply hfaith
    simp only [map_mul, hv, hc]
    exact cubic_commutes_diagonal a
  · apply hfaith
    simp only [map_pow, hc, map_one]
    exact cubic_pow_three
  · intro p _ hp
    rw [hc] at hp
    exact cubic_fixed_free p hp

/-- The actual distributivity equivalence for the binary tensor product. -/
def coordinates : ((ZMod 2 × ZMod 2) ⊗[ZMod 2] W) ≃ₗ[ZMod 2] (W × W) :=
  (TensorProduct.prodLeft (ZMod 2) (ZMod 2) (ZMod 2) (ZMod 2) W).trans
    ((TensorProduct.lid (ZMod 2) W).prodCongr (TensorProduct.lid (ZMod 2) W))

/-- Intertwining for an actor confined to the second tensor factor. -/
lemma coordinates_diagonal (a : Module.End (ZMod 2) W)
    (z : (ZMod 2 × ZMod 2) ⊗[ZMod 2] W) :
    coordinates (TensorProduct.map 1 a z) = diagonal a (coordinates z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rcases x with ⟨u, v⟩
    simp [coordinates, diagonal]
  | add x y hx hy => simp [hx, hy]

/-- Intertwining for a swap tensored with an arbitrary operator. -/
lemma coordinates_mixed (a : Module.End (ZMod 2) W)
    (z : (ZMod 2 × ZMod 2) ⊗[ZMod 2] W) :
    coordinates (TensorProduct.map (mixed 1) a z) = mixed a (coordinates z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rcases x with ⟨u, v⟩
    simp [coordinates, mixed]
  | add x y hx hy => simp [hx, hy]

/-- Intertwining for the cubic actor in the first tensor factor. -/
lemma coordinates_cubic (z : (ZMod 2 × ZMod 2) ⊗[ZMod 2] W) :
    coordinates (TensorProduct.map cubic 1 z) = cubic (coordinates z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rcases x with ⟨u, v⟩
    simp [coordinates, cubic, add_smul]
  | add x y hx hy => simp [hx, hy]
end Representation.RankTwo.TensorCoordinates

