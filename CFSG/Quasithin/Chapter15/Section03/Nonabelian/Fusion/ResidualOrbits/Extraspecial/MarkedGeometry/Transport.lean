module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.MarkedGeometry.Square
public import Mathlib.Algebra.Module.ZMod
/-!
# Transporting the earlier orthogonal square space

A multiplicative equivalence from the literal U/Z to the additive group of a
binary quadratic space compares linearly with the natural/dual recognition.
Pullback transports the actual power-map identity and polar nondegeneracy.
This supplies `SquareForm` from the geometric statement of 15.3.56(1), without
assuming that its quadratic form is already the evaluation pairing.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.56(1) and 15.3.58(3), printed pp.1147–1149.
-/

@[expose] public section
open Subgroup BinaryNaturalDual BinaryNaturalDual.ModelOrbits
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial
variable {G : Type*} [Group G] {T Z ZS V : Subgroup G} {t z : G}
variable [(Z.subgroupOf (closureU Z ZS)).Normal]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- Any additive coordinates on the actual quotient compare linearly over F₂. -/
noncomputable def squareCoordinateChange (d : RecognizedAction T Z ZS V t)
    (e : VectorQuotient Z ZS ≃* Multiplicative W) : NaturalDualSpace ≃ₗ[ZMod 2] W := by
  let a : NaturalDualSpace ≃+ W := {
    toEquiv := Multiplicative.ofAdd.trans
      ((d.coordinates.symm.trans e).toEquiv.trans Multiplicative.toAdd)
    map_add' x y := by
      change (e (d.coordinates.symm (Multiplicative.ofAdd (x + y)))).toAdd = _
      rw [ofAdd_add, map_mul, map_mul, toAdd_mul]
      rfl }
  exact LinearEquiv.ofBijective (a.toAddMonoidHom.toZModLinearMap 2) a.bijective

/-- Construct the coordinate form from the orthogonal power-map space of
15.3.56(1), on any actual additive model of U/Z. This proves the transport
of both the square equation and polar nondegeneracy. -/
noncomputable def SquareForm.of_orthogonalSpace (d : RecognizedAction T Z ZS V t)
    (e : VectorQuotient Z ZS ≃* Multiplicative W) (Q : QuadraticForm (ZMod 2) W)
    (hnd : Q.polarBilin.Nondegenerate)
    (hsquare : ∀ x : closureU Z ZS, (x : G) ^ 2 =
      z ^ (Q (e (QuotientGroup.mk' _ x)).toAdd).val) : SquareForm d z where
  form := Q.comp (squareCoordinateChange d e).toLinearMap
  nondegenerate := by
    let L := squareCoordinateChange d e
    rw [QuadraticMap.polarBilin_comp]
    constructor
    · intro x hx
      apply L.injective
      rw [map_zero]
      apply hnd.1
      intro w
      obtain ⟨y, rfl⟩ := L.surjective w
      exact hx y
    · intro x hx
      apply L.injective
      rw [map_zero]
      apply hnd.2
      intro w
      obtain ⟨y, rfl⟩ := L.surjective w
      exact hx y
  square x := by
    rw [hsquare]
    congr 2
    change Q (e (QuotientGroup.mk' _ x)).toAdd =
      Q (e (d.coordinates.symm (d.coordinates (QuotientGroup.mk' _ x)))).toAdd
    rw [d.coordinates.symm_apply_apply]
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial
