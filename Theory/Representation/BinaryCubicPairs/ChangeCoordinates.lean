module

public import Theory.Representation.BinaryCubicPairs.FixedCount

/-!
# Changing coordinates on the four-dimensional support

Simultaneous matrix conjugation preserves the original group representation,
its fixed kernels, and the sum of the two displacement ranges. The inclusion
of the supporting space is changed by the inverse coordinate map, so the
ambient module itself is unchanged.

Source application: Aschbacher--Smith E.6.24, printed p.255.
-/

@[expose] public section
namespace BinaryCubicPairs
open Packed

variable {G : Type*} [Group G] (μ : G →* CoordinateMatrix)
  (g h : CoordinateMatrix) (hgh : g * h = 1) (hhg : h * g = 1)

def conjugatedHom : G →* CoordinateMatrix where
  toFun a := g * μ a * h
  map_one' := by simp only [map_one, mul_one, hgh]
  map_mul' a b := by
    simp only [map_mul]
    calc
      _ = g * μ a * (h * g) * μ b * h := by rw [hhg]; simp only [mul_one, mul_assoc]
      _ = _ := by simp only [mul_assoc]

include hgh hhg

theorem conjugatedHom_injective (hμ : Function.Injective μ) :
    Function.Injective (conjugatedHom μ g h hgh hhg) := by
  intro a b hab
  apply hμ
  have he := congrArg (fun M : CoordinateMatrix => h * M * g) hab
  change h * (g * μ a * h) * g = h * (g * μ b * h) * g at he
  have he' : h * (g * μ a * h) * g = μ a := by
    calc
      _ = (h * g) * μ a * (h * g) := by simp only [mul_assoc]
      _ = μ a := by rw [hhg, one_mul, mul_one]
  have he'' : h * (g * μ b * h) * g = μ b := by
    calc
      _ = (h * g) * μ b * (h * g) := by simp only [mul_assoc]
      _ = μ b := by rw [hhg, one_mul, mul_one]
  exact he'.symm.trans (he.trans he'')

def coordinateEquiv : CoordinateVector ≃ₗ[ZMod 2] CoordinateVector :=
  Matrix.toLin'OfInv hhg hgh

theorem coordinateEquiv_apply (x : CoordinateVector) :
    coordinateEquiv g h hgh hhg x = g.mulVec x := rfl

theorem coordinateEquiv_symm_apply (x : CoordinateVector) :
    (coordinateEquiv g h hgh hhg).symm x = h.mulVec x := rfl

def fixedKernelEquiv (M : CoordinateMatrix) :
    fixedKernel M ≃ₗ[ZMod 2] fixedKernel (g * M * h) where
  toFun x := ⟨g.mulVec x, by
    change (g * M * h).mulVec (g.mulVec x.val) - g.mulVec x.val = 0
    have hx : M.mulVec x.val = x.val := sub_eq_zero.mp x.property
    rw [Matrix.mulVec_mulVec, mul_assoc, mul_assoc, hhg, mul_one,
      ← Matrix.mulVec_mulVec, hx, sub_self]⟩
  invFun x := ⟨h.mulVec x, by
    change M.mulVec (h.mulVec x.val) - h.mulVec x.val = 0
    have hx : (g * M * h).mulVec x.val = x.val := sub_eq_zero.mp x.property
    have he := congrArg (Matrix.mulVec h) hx
    rw [Matrix.mulVec_mulVec, ← mul_assoc, ← mul_assoc, hhg, one_mul,
      ← Matrix.mulVec_mulVec] at he
    exact sub_eq_zero.mpr he⟩
  left_inv x := by
    apply Subtype.ext
    change h.mulVec (g.mulVec x.val) = x.val
    rw [Matrix.mulVec_mulVec, hhg, Matrix.one_mulVec]
  right_inv x := by
    apply Subtype.ext
    change g.mulVec (h.mulVec x.val) = x.val
    rw [Matrix.mulVec_mulVec, hgh, Matrix.one_mulVec]
  map_add' x y := by
    apply Subtype.ext
    change g.mulVec (x.val + y.val) = g.mulVec x.val + g.mulVec y.val
    exact Matrix.mulVec_add _ _ _
  map_smul' r x := by
    apply Subtype.ext
    change g.mulVec (r • x.val) = r • g.mulVec x.val
    exact Matrix.mulVec_smul _ _ _

theorem conjugated_full (c d : G)
    (hfull : ∀ v : CoordinateVector, ∃ x y : CoordinateVector,
      (μ c).mulVec x - x + ((μ d).mulVec y - y) = v) :
    ∀ v : CoordinateVector, ∃ x y : CoordinateVector,
      (conjugatedHom μ g h hgh hhg c).mulVec x - x +
        ((conjugatedHom μ g h hgh hhg d).mulVec y - y) = v := by
  intro v
  obtain ⟨x, y, hxy⟩ := hfull (h.mulVec v)
  refine ⟨g.mulVec x, g.mulVec y, ?_⟩
  change (g * μ c * h).mulVec (g.mulVec x) - g.mulVec x +
    ((g * μ d * h).mulVec (g.mulVec y) - g.mulVec y) = v
  calc
    _ = g.mulVec ((μ c).mulVec x - x + ((μ d).mulVec y - y)) := by
      have h1 (z : CoordinateVector) (M : CoordinateMatrix) :
          (g * M * h).mulVec (g.mulVec z) = g.mulVec (M.mulVec z) := by
        rw [Matrix.mulVec_mulVec]
        have he : g * M * h * g = g * M := by rw [mul_assoc, hhg, mul_one]
        rw [he, Matrix.mulVec_mulVec]
      rw [h1, h1, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_sub]
    _ = v := by rw [hxy, Matrix.mulVec_mulVec, hgh, Matrix.one_mulVec]

end BinaryCubicPairs
