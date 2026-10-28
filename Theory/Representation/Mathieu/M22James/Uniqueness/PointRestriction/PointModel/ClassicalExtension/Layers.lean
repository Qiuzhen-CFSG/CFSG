module

import Mathlib.Tactic.FinCases
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.ClassicalExtension.Multiplication
/-!
# The natural submodule and the binary dual quotient

The first-coordinate inclusion and second-coordinate projection form an
exact sequence of actual representations. Over F₄ its quotient is the
Frobenius inverse-transpose natural action. Coordinatewise Frobenius removes
this twist over F₂. The nondegenerate binary pairing given by the real
coefficient of the field dot product then identifies the quotient with the
actual F₂-linear dual of the natural module.

Source: the natural-by-dual point restriction in Aschbacher–Smith H.12.1,
printed p.394, in the setting of James (1973), Lemma 8.3.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel.Reference
open Matrix

/-- Inclusion of the actual natural field representation. -/
def naturalInclusion : (Representation.specialLinearNatural 3 (k := F)).IntertwiningMap
    representation :=
  (LinearMap.inl F W W).intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g w
    exact (operator_inclusion g w).symm)

/-- The quotient map onto the Frobenius inverse-transpose natural representation. -/
def quotientProjection : representation.IntertwiningMap quotientRepresentation :=
  (LinearMap.snd F W W).intertwiningMap_of_isIntertwiningMap _ _ (by intro g v; rfl)

lemma naturalInclusion_injective : Function.Injective naturalInclusion := by
  intro u v h
  exact congrArg Prod.fst h

lemma quotientProjection_surjective : Function.Surjective quotientProjection :=
  fun w => ⟨(0,w), rfl⟩

/-- Exactness identifies the first block as precisely the kernel of the quotient. -/
lemma natural_quotient_exact :
    LinearMap.range naturalInclusion.toLinearMap = LinearMap.ker quotientProjection.toLinearMap := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    rfl
  · intro hv
    exact ⟨v.1, Prod.ext rfl (LinearMap.mem_ker.mp hv).symm⟩

/-- The quotient action, with its binary scalars. -/
def binaryQuotientRepresentation : Representation (ZMod 2) SL W where
  toFun g := (quotientRepresentation g).restrictScalars (ZMod 2)
  map_one' := by
    apply LinearMap.ext
    intro w
    exact LinearMap.congr_fun quotientRepresentation.map_one w
  map_mul' g h := by
    apply LinearMap.ext
    intro w
    exact LinearMap.congr_fun (quotientRepresentation.map_mul g h) w

/-- The same inclusion over the binary field. -/
def binaryNaturalInclusion : Representation.SL3FourNaturalDual.natural.IntertwiningMap
    binaryRepresentation :=
  (LinearMap.inl (ZMod 2) W W).intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g w
    exact (operator_inclusion g w).symm)

/-- The same quotient map over the binary field. -/
def binaryQuotientProjection : binaryRepresentation.IntertwiningMap binaryQuotientRepresentation :=
  (LinearMap.snd (ZMod 2) W W).intertwiningMap_of_isIntertwiningMap _ _ (by intro g v; rfl)

lemma binaryNaturalInclusion_injective : Function.Injective binaryNaturalInclusion := by
  intro u v h
  exact congrArg Prod.fst h

lemma binaryQuotientProjection_surjective : Function.Surjective binaryQuotientProjection :=
  fun w => ⟨(0,w), rfl⟩

lemma binary_natural_quotient_exact :
    LinearMap.range binaryNaturalInclusion.toLinearMap =
      LinearMap.ker binaryQuotientProjection.toLinearMap := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    rfl
  · intro hv
    exact ⟨v.1, Prod.ext rfl (LinearMap.mem_ker.mp hv).symm⟩

/-- Coordinatewise Frobenius removes the quotient twist over the binary field. -/
def quotientUntwist : W ≃ₗ[ZMod 2] W where
  toFun w i := Representation.SL2FourNatural.fieldFrobenius (w i)
  invFun w i := Representation.SL2FourNatural.fieldFrobenius (w i)
  left_inv w := by funext i; exact Representation.SL2FourNatural.fieldFrobenius_involutive _
  right_inv w := by funext i; exact Representation.SL2FourNatural.fieldFrobenius_involutive _
  map_add' u v := by funext i; exact map_add _ _ _
  map_smul' c w := by
    funext i
    fin_cases c
    · change Representation.SL2FourNatural.fieldFrobenius ((0 : ZMod 2) • w i) =
        (0 : ZMod 2) • Representation.SL2FourNatural.fieldFrobenius (w i)
      simp
    · change Representation.SL2FourNatural.fieldFrobenius ((1 : ZMod 2) • w i) =
        (1 : ZMod 2) • Representation.SL2FourNatural.fieldFrobenius (w i)
      simp

lemma quotientUntwist_equivariant (g : SL) (w : W) :
    quotientUntwist (binaryQuotientRepresentation g w) =
      Representation.SL3FourNaturalDual.dualCoordinates g (quotientUntwist w) := by
  funext i
  change Representation.SL2FourNatural.fieldFrobenius
    (∑ j, Representation.SL2FourNatural.fieldFrobenius (g⁻¹.val j i) * w j) =
    ∑ j, g⁻¹.val j i * Representation.SL2FourNatural.fieldFrobenius (w j)
  simp only [map_sum, map_mul, Representation.SL2FourNatural.fieldFrobenius_involutive]

/-- The twisted quotient is the concrete binary inverse-transpose module. -/
def quotientUntwistEquiv : binaryQuotientRepresentation.Equiv
    Representation.SL3FourNaturalDual.dualCoordinates :=
  Representation.Equiv.mk quotientUntwist (by
    intro g
    apply LinearMap.ext
    exact quotientUntwist_equivariant g)

/-- A nondegenerate binary pairing, obtained by taking the real coefficient of
 the field dot product. -/
def binaryDualMap : W →ₗ[ZMod 2] Module.Dual (ZMod 2) W where
  toFun w := (QuadraticAlgebra.reₗ 1 1).comp
    (((dotProductEquiv F (Fin 3)) w).restrictScalars (ZMod 2))
  map_add' u v := by
    apply LinearMap.ext
    intro w
    change ((u + v) ⬝ᵥ w).re = (u ⬝ᵥ w).re + (v ⬝ᵥ w).re
    rw [add_dotProduct]
    rfl
  map_smul' a v := by
    apply LinearMap.ext
    intro w
    change (a • v ⬝ᵥ w).re = a • (v ⬝ᵥ w).re
    rw [smul_dotProduct]
    rfl

lemma binaryDualMap_apply (u v : W) : binaryDualMap u v = (u ⬝ᵥ v).re := rfl

lemma binaryDualMap_injective : Function.Injective binaryDualMap := by
  intro u v h
  have hc (i : Fin 3) (a : F) : (u i * a).re = (v i * a).re := by
    simpa only [binaryDualMap_apply, dotProduct_single] using
      congrArg (fun f : Module.Dual (ZMod 2) W => f (Pi.single i a)) h
  funext i
  apply QuadraticAlgebra.ext
  · simpa only [mul_one] using hc i 1
  · simpa using hc i QuadraticAlgebra.omega

/-- Inverse-transpose coordinates represent the actual binary linear dual. -/
def binaryDualCoordinates : W ≃ₗ[ZMod 2] Module.Dual (ZMod 2) W :=
  LinearEquiv.ofBijective binaryDualMap ⟨binaryDualMap_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ZMod 2) (V := W)).symm).mp binaryDualMap_injective⟩

lemma binaryDualCoordinates_equivariant (g : SL) (w : W) :
    binaryDualCoordinates (Representation.SL3FourNaturalDual.dualCoordinates g w) =
      Representation.SL3FourNaturalDual.natural.dual g (binaryDualCoordinates w) := by
  apply LinearMap.ext
  intro v
  change (((g⁻¹).val.transpose *ᵥ w) ⬝ᵥ v).re = (w ⬝ᵥ ((g⁻¹).val *ᵥ v)).re
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec]

/-- The quotient is the genuine binary dual of the first block. -/
def binaryQuotientDualEquiv : binaryQuotientRepresentation.Equiv
    Representation.SL3FourNaturalDual.natural.dual :=
  quotientUntwistEquiv.trans (Representation.Equiv.mk binaryDualCoordinates (by
    intro g
    apply LinearMap.ext
    exact binaryDualCoordinates_equivariant g))
end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel.Reference
