module

public import Theory.Representation.MathieuCodeRestriction.Orthogonality
public import Theory.Representation.MathieuCodeRestriction
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Perfect duality of the native Mathieu code and cocode

The coordinate dot product descends through the constant line on the Golay
side and through Golay on the even-core side. Self-duality of Golay and the
double-orthogonal identity prove that the resulting pairing is nondegenerate
in both variables. It therefore gives actual intertwining equivalences with
the contragredient actions, for M₂₄ and its native M₂₃ point stabilizer.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.13.1,
printed p.395. This constructs the duality maps; no irreducibility or local
fixed-space dimensions are assumed.
-/

@[expose] public section

noncomputable section
open Sporadic.Mathieu
namespace MathieuCode

private def rawPairing : golay →ₗ[ZMod 2] Module.Dual (ZMod 2) Core :=
  Core.dualRestrict.comp (LinearMap.comp dotForm golay.subtype)

private theorem rawPairing_codeLine : codeLine ≤ rawPairing.ker := by
  intro v hv
  apply LinearMap.ext
  intro w
  have hw : w.val ∈ BinaryPermutation.core (Fin 24) := w.property
  rw [core_eq_orthogonal_constants] at hw
  exact hw v.val hv

private theorem rawPairing_codeInCore : codeInCore ≤ rawPairing.flip.ker := by
  intro w hw
  apply LinearMap.ext
  intro v
  exact golay_le_orthogonal hw v.val v.property

/-- Intersection parity descends to the actual eleven-dimensional quotients. -/
def codeCocodePairing : Code →ₗ[ZMod 2] Module.Dual (ZMod 2) Cocode :=
  (Core.dualRestrict.comp (LinearMap.comp dotForm golay.subtype)).liftQ₂
    codeLine codeInCore (by exact rawPairing_codeLine) (by exact rawPairing_codeInCore)

@[simp] theorem codeCocodePairing_mk (v : golay) (w : Core) :
    codeCocodePairing (codeLine.mkQ v) (codeInCore.mkQ w) = dotForm v.val w.val := rfl

/-- Nondegeneracy on the cocode follows from self-duality of Golay. -/
theorem codeCocodePairing_right_nondegenerate (w : Cocode)
    (hw : ∀ v, codeCocodePairing v w = 0) : w = 0 := by
  induction w using Submodule.Quotient.induction_on with
  | _ w =>
    apply (Submodule.Quotient.mk_eq_zero codeInCore).mpr
    change w.val ∈ golay
    rw [← golay_orthogonal_eq]
    intro v hv
    exact hw (codeLine.mkQ ⟨v, hv⟩)

/-- Nondegeneracy on the code follows from the orthogonal of the even core. -/
theorem codeCocodePairing_left_nondegenerate (v : Code)
    (hv : ∀ w, codeCocodePairing v w = 0) : v = 0 := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    apply (Submodule.Quotient.mk_eq_zero codeLine).mpr
    change v.val ∈ BinaryPermutation.constants (Fin 24)
    rw [← dotForm.orthogonal_orthogonal dotForm_nondegenerate dotForm_symmetric.isRefl
      (BinaryPermutation.constants (Fin 24)),
      ← core_eq_orthogonal_constants]
    intro w hw
    rw [dotForm_symmetric.eq]
    exact hv (codeInCore.mkQ ⟨w, hw⟩)

theorem codeCocodePairing_injective : Function.Injective codeCocodePairing := by
  intro v w h
  apply sub_eq_zero.mp
  apply codeCocodePairing_left_nondegenerate
  intro x
  rw [map_sub, h, sub_self, LinearMap.zero_apply]

theorem codeCocodePairing_flip_injective : Function.Injective codeCocodePairing.flip := by
  intro v w h
  apply sub_eq_zero.mp
  apply codeCocodePairing_right_nondegenerate
  intro x
  change (codeCocodePairing.flip (v - w)) x = 0
  rw [map_sub, h, sub_self, LinearMap.zero_apply]

theorem codeCocodePairing_invariant (g : M24) (v : Code) (w : Cocode) :
    codeCocodePairing (codeRepresentation g v) (cocodeRepresentation g w) =
      codeCocodePairing v w := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    induction w using Submodule.Quotient.induction_on with
    | _ w => exact dotForm_invariant g v.val w.val

private def codeDualMap : codeRepresentation.IntertwiningMap cocodeRepresentation.dual where
  toLinearMap := codeCocodePairing
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change codeCocodePairing (codeRepresentation g v) w =
      codeCocodePairing v (cocodeRepresentation g⁻¹ w)
    have h := codeCocodePairing_invariant g v (cocodeRepresentation g⁻¹ w)
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] using h

private def cocodeDualMap : cocodeRepresentation.IntertwiningMap codeRepresentation.dual where
  toLinearMap := codeCocodePairing.flip
  isIntertwining' g := by
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro v
    change codeCocodePairing v (cocodeRepresentation g w) =
      codeCocodePairing (codeRepresentation g⁻¹ v) w
    have h := codeCocodePairing_invariant g (codeRepresentation g⁻¹ v) w
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] using h

/-- The native code is the contragredient of the native cocode, by the coordinate pairing. -/
def codeDuality : codeRepresentation.Equiv cocodeRepresentation.dual :=
  (show codeRepresentation.IntertwiningMap cocodeRepresentation.dual from
    { toLinearMap := codeCocodePairing
      isIntertwining' := by exact codeDualMap.isIntertwining' }).ofBijective
    ⟨codeCocodePairing_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Subspace.dual_finrank_eq, finrank_code, finrank_cocode])).mp
        codeCocodePairing_injective⟩

/-- The native cocode is the contragredient of the native code. -/
def cocodeDuality : cocodeRepresentation.Equiv codeRepresentation.dual :=
  (show cocodeRepresentation.IntertwiningMap codeRepresentation.dual from
    { toLinearMap := codeCocodePairing.flip
      isIntertwining' := by exact cocodeDualMap.isIntertwining' }).ofBijective
    ⟨codeCocodePairing_flip_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Subspace.dual_finrank_eq, finrank_code, finrank_cocode])).mp
        codeCocodePairing_flip_injective⟩

@[simp] theorem codeDuality_apply (v : Code) (w : Cocode) :
    codeDuality v w = codeCocodePairing v w := rfl

@[simp] theorem cocodeDuality_apply (w : Cocode) (v : Code) :
    cocodeDuality w v = codeCocodePairing v w := rfl

/-- Restriction of the same pairing to the native M₂₃ point stabilizer. -/
def m23CodeDuality : m23CodeRepresentation.Equiv m23CocodeRepresentation.dual :=
  Representation.Equiv.mk (ρ := m23CodeRepresentation)
    (σ := m23CocodeRepresentation.dual) codeDuality.toLinearEquiv (by
      intro g
      apply LinearMap.ext
      intro v
      apply LinearMap.ext
      intro w
      change codeCocodePairing (codeRepresentation (pointEmbedding g) v) w =
        codeCocodePairing v (cocodeRepresentation (pointEmbedding g⁻¹) w)
      rw [map_inv]
      exact LinearMap.congr_fun
        (LinearMap.congr_fun (codeDualMap.isIntertwining' (pointEmbedding g)) v) w)

/-- Reverse duality for the native M₂₃ point stabilizer. -/
def m23CocodeDuality : m23CocodeRepresentation.Equiv m23CodeRepresentation.dual :=
  Representation.Equiv.mk (ρ := m23CocodeRepresentation)
    (σ := m23CodeRepresentation.dual) cocodeDuality.toLinearEquiv (by
      intro g
      apply LinearMap.ext
      intro w
      apply LinearMap.ext
      intro v
      change codeCocodePairing v (cocodeRepresentation (pointEmbedding g) w) =
        codeCocodePairing (codeRepresentation (pointEmbedding g⁻¹) v) w
      rw [map_inv]
      exact LinearMap.congr_fun
        (LinearMap.congr_fun (cocodeDualMap.isIntertwining' (pointEmbedding g)) w) v)

end MathieuCode
