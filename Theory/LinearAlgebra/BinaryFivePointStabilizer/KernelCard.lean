module

public import Theory.LinearAlgebra.BinaryFivePointStabilizer.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Order of the binary point-stabilizer kernel

Displacement identifies the actual quotient-action kernel with the additive
space of linear maps from the quotient to the fixed line. The inverse sends a
map `f` to the shear `x ↦ x + f (mkQ x)`. Composition adds displacements because
the stabilizer fixes the line pointwise. For a nonzero marked vector in a
five-dimensional binary space, this map space has dimension four and order 16.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma 14.2.21, printed p.989 (PDF p.1006).
-/

public section

namespace Theory.LinearAlgebra.BinaryFivePointStabilizer
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- Displacement, factored through the quotient by the fixed line. -/
def kernelDisplacement (z : E) (g : kernel z) :
    QuotientSpace z →ₗ[ZMod 2] line z :=
  (line z).liftQ
    ((g.val.val.toLinearMap - LinearMap.id).codRestrict (line z)
      ((mem_kernel_iff z g.val).mp g.property)) (by
        intro x hx
        apply Subtype.ext
        change g.val.val x - x = 0
        exact sub_eq_zero.mpr (fixes_line z g.val x hx))

@[simp] theorem kernelDisplacement_mk (z : E) (g : kernel z) (x : E) :
    (kernelDisplacement z g ((line z).mkQ x) : E) = g.val.val x - x := by rfl

private def kernelShearLinearEquiv (z : E) (f : QuotientSpace z →ₗ[ZMod 2] line z) :
    E ≃ₗ[ZMod 2] E where
  toLinearMap := LinearMap.id + (line z).subtype.comp (f.comp (line z).mkQ)
  invFun x := x - (f ((line z).mkQ x) : E)
  left_inv x := by
    change x + (f ((line z).mkQ x) : E) -
      (f ((line z).mkQ (x + (f ((line z).mkQ x) : E))) : E) = x
    have hq : (line z).mkQ (f ((line z).mkQ x) : E) = 0 :=
      (Submodule.Quotient.mk_eq_zero (line z)).mpr (f ((line z).mkQ x)).property
    rw [map_add, hq, add_zero, add_sub_cancel_right]
  right_inv x := by
    change x - (f ((line z).mkQ x) : E) +
      (f ((line z).mkQ (x - (f ((line z).mkQ x) : E))) : E) = x
    have hq : (line z).mkQ (f ((line z).mkQ x) : E) = 0 :=
      (Submodule.Quotient.mk_eq_zero (line z)).mpr (f ((line z).mkQ x)).property
    rw [map_sub, hq, sub_zero, sub_add_cancel]

/-- The shear associated to a linear map from the quotient to the fixed line. -/
def kernelShear (z : E) (f : QuotientSpace z →ₗ[ZMod 2] line z) : kernel z :=
  ⟨⟨kernelShearLinearEquiv z f, by
    change z + (f ((line z).mkQ z) : E) = z
    have hz : (line z).mkQ z = 0 :=
      (Submodule.Quotient.mk_eq_zero (line z)).mpr (Submodule.mem_span_singleton_self z)
    simp [hz]⟩, by
      apply (mem_kernel_iff z _).mpr
      intro x
      change x + (f ((line z).mkQ x) : E) - x ∈ line z
      simpa only [add_sub_cancel_left] using (f ((line z).mkQ x)).property⟩

@[simp] theorem kernelShear_apply (z : E) (f : QuotientSpace z →ₗ[ZMod 2] line z)
    (x : E) : (kernelShear z f).val.val x = x + (f ((line z).mkQ x) : E) := by rfl

/-- Composition in the kernel corresponds to addition of quotient-to-line maps. -/
def kernelDisplacementEquiv (z : E) :
    kernel z ≃* Multiplicative (QuotientSpace z →ₗ[ZMod 2] line z) where
  toFun g := Multiplicative.ofAdd (kernelDisplacement z g)
  invFun f := kernelShear z (Multiplicative.toAdd f)
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    ext x
    change x + (kernelDisplacement z g ((line z).mkQ x) : E) = g.val.val x
    rw [kernelDisplacement_mk]
    abel
  right_inv f := by
    change kernelDisplacement z (kernelShear z (Multiplicative.toAdd f)) =
      Multiplicative.toAdd f
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      apply Subtype.ext
      change (kernelDisplacement z (kernelShear z (Multiplicative.toAdd f))
        ((line z).mkQ x) : E) = _
      rw [kernelDisplacement_mk, kernelShear_apply, add_sub_cancel_left]
      rfl
  map_mul' g h := by
    change kernelDisplacement z (g * h) = kernelDisplacement z g + kernelDisplacement z h
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      apply Subtype.ext
      change (kernelDisplacement z (g * h) ((line z).mkQ x) : E) =
        (kernelDisplacement z g ((line z).mkQ x) : E) +
        (kernelDisplacement z h ((line z).mkQ x) : E)
      simp only [kernelDisplacement_mk]
      change g.val.val (h.val.val x) - x = (g.val.val x - x) + (h.val.val x - x)
      have hf := fixes_line z g.val (h.val.val x - x)
        ((mem_kernel_iff z h.val).mp h.property x)
      rw [map_sub] at hf
      rw [sub_eq_iff_eq_add.mp hf]
      abel

@[simp] theorem kernelDisplacementEquiv_apply (z : E) (g : kernel z) :
    kernelDisplacementEquiv z g = Multiplicative.ofAdd (kernelDisplacement z g) := by rfl

@[simp] theorem kernelDisplacementEquiv_symm_apply (z : E)
    (f : Multiplicative (QuotientSpace z →ₗ[ZMod 2] line z)) :
    (kernelDisplacementEquiv z).symm f = kernelShear z (Multiplicative.toAdd f) := by rfl

/-- The actual quotient-action kernel in a binary five-space has order sixteen. -/
theorem natCard_kernel [FiniteDimensional (ZMod 2) E] (z : E) (hz : z ≠ 0)
    (hE : Module.finrank (ZMod 2) E = 5) : Nat.card (kernel z) = 16 := by
  rw [Nat.card_congr (kernelDisplacementEquiv z).toEquiv]
  change Nat.card (QuotientSpace z →ₗ[ZMod 2] line z) = 16
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Module.finrank_linearMap,
    finrank_quotient z hz hE, finrank_span_singleton hz]
  norm_num

end Theory.LinearAlgebra.BinaryFivePointStabilizer
