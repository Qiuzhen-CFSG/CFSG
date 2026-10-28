module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.TerminalWeights.Models
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.MarkedSections.Orthogonal
public import Mathlib.LinearAlgebra.Prod
/-!
# Split coordinates over the restriction field

Entrywise transport through the actual restriction isomorphism gives matrix
coordinates for the canonical compatible module. Conjugating the first SL2
factor diagonalizes its action into two row planes with reciprocal coefficients.
All coefficients and orders use the same field isomorphism as the common plane.
The source-plane constructor consumes these coordinates with the actual generator.

Source: Aschbacher--Smith, Proposition 11.3.2, final paragraph, printed p.775.
-/

open Subgroup Representation Matrix
open ClassicalOrthogonal.FourPlusMatrix
open scoped IsMulCommutative MatrixGroups
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights
section Coordinates
variable {E F M : Type*} [Field E] [Field F] [Finite F] [AddCommGroup M] [Module E M]
    (N : NaturalPlane (E := E) (F := F) (A := M)) (hc : Nat.card E = Nat.card F)
    (e : M ≃ₗ[E] Mat (F := E))

/-- Matrix coordinates over the exact restriction field, preserving the
canonical module on their domain. -/
def compatibleCoordinates :
    let := N.compatibleModule hc
    M ≃ₗ[F] Mat (F := F) := by
  let := N.compatibleModule hc
  let φ := N.fieldEquiv hc
  exact {
    toFun := fun p => (e p).map φ
    invFun := fun v => e.symm (v.map φ.symm)
    left_inv := by
      intro p
      change e.symm (((e p).map φ).map φ.symm) = p
      have h : ((e p).map φ).map φ.symm = e p := by ext i j; simp
      rw [h,e.symm_apply_apply]
    right_inv := by
      intro p
      change (e (e.symm (p.map φ.symm))).map φ = p
      rw [e.apply_symm_apply]
      ext i j
      simp
    map_add' := by
      intro p q
      ext i j
      simp
    map_smul' := by
      intro a p
      change (e (φ.symm a • p)).map φ = a • (e p).map φ
      rw [map_smul]
      ext i j
      simp [Matrix.map_apply] }

end Coordinates
section Split
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G F : Type*} [Group G] [Field F] [Finite F]
    {E : BinaryField} {P Y : Subgroup G} [IsMulCommutative P]
    (o : MarkedSections.OrthogonalMarking E P Y)
    (N : let := o.moduleStructure; NaturalPlane (E := E.Carrier) (F := F) (A := Additive P))
    (hc : Nat.card E.Carrier = Nat.card F)

/-- Diagonalize the actual first-factor action in coordinates over the
restriction isomorphism; the field on P is not replaced by another module. -/
theorem compatible_split_coordinates (y : Y) (hy : (o.actors y).2 = 1)
    (b : SL(2,E.Carrier)) (a : E.Carrier)
    (hdiag : (b * (o.actors y).1 * b⁻¹).val = !![a,0;0,a⁻¹]) :
    let := o.moduleStructure
    let := N.compatibleModule hc
    let φ := N.fieldEquiv hc
    ∃ e : Additive P ≃ₗ[F] ((Fin 2 → F) × (Fin 2 → F)),
      ∀ p, e (N.compatibleRepresentation hc o.action y p) =
        (φ a • (e p).1, (φ a)⁻¹ • (e p).2) := by
  let := o.moduleStructure
  let e₀ := o.coordinates.linearEquiv E.Carrier
  let e₁ := e₀.trans (matrixAction (b,1))
  have he₁ (p : Additive P) : e₁ p = b.val * e₀ p := by
    change b.val * e₀ p * (1 : SL(2,E.Carrier))⁻¹.val = _
    simp
  have he₀ (p : Additive P) : e₀ (o.action y p) = (o.actors y).1.val * e₀ p := by
    have hh : e₀ (o.action y p) = representation (o.actors y) (e₀ p) := e₀.apply_symm_apply _
    rw [hh,representation_apply,hy]
    simp
  have hd : b.val * (o.actors y).1.val = !![a,0;0,a⁻¹] * b.val := by
    have hh := congrArg (fun M : Mat (F := E.Carrier) => M * b.val) hdiag
    simpa only [Matrix.SpecialLinearGroup.coe_mul, mul_assoc,
      ← Matrix.SpecialLinearGroup.coe_mul b⁻¹ b, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one,mul_one] using hh
  have he (p : Additive P) : e₁ (o.action y p) = !![a,0;0,a⁻¹] * e₁ p := by
    rw [he₁,he₀,←mul_assoc,hd,mul_assoc,←he₁]
  let := N.compatibleModule hc
  let φ := N.fieldEquiv hc
  let ec := compatibleCoordinates N hc e₁
  let e := ec.trans (LinearEquiv.finTwoArrow F (Fin 2 → F))
  refine ⟨e,fun p => ?_⟩
  apply Prod.ext <;> ext j
  · change φ (e₁ (o.action y p) 0 j) = φ a * φ (e₁ p 0 j)
    rw [he]
    simp [Matrix.mul_apply,Fin.sum_univ_two]
  · change φ (e₁ (o.action y p) 1 j) = (φ a)⁻¹ * φ (e₁ p 1 j)
    rw [he]
    simp [Matrix.mul_apply,Fin.sum_univ_two]
end Split
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.TerminalWeights
