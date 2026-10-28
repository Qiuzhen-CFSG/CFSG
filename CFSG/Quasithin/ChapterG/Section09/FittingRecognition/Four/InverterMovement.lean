module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.InverterFixedPoints
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.OrthogonalOrder

/-!
# Applying the residual inverter to the original orthogonal action

A full orthogonal realization transports the original two-residual and its
inverter to the binary-plane wreath model. The fixed-vector bound then
moves a vector in the original marked subspace of dimension at least three.
All group, action and subspace parameters are retained.

Source application: Aschbacher--Smith, 14.3.15, printed p.994.
-/

public section
open Subgroup Module
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- An inverter of the original full orthogonal residual moves the given
three-dimensional subspace under the original representation. -/
theorem residual_inverter_moves_of_full_orthogonal
    (ρ : Representation (ZMod 2) G V) (hρ : OrthogonalRealization ρ ⊤)
    (r : G) (hr : orderOf r = 2)
    (hinv : ∀ x ∈ pResidual 2 G, r*x*r⁻¹=x⁻¹)
    (S : Submodule (ZMod 2) V) (hd : 3 ≤ finrank (ZMod 2) S) :
    ∃ v ∈ S, ρ r v ≠ v := by
  obtain ⟨e,l,he⟩ := hρ
  let k : G ≃* BinaryFourPlus.Wreath :=
    ((e.trans topEquiv).trans splitOrthogonalEquiv).trans BinaryFourPlus.isometryEquivWreath
  let f := l.trans splitCoordinates
  have hact (g : G) (v : V) :
      (BinaryFourPlus.wreathToIsometry (k g)).val (f v) = f (ρ g v) := by
    change (BinaryFourPlus.wreathToIsometry
      (BinaryFourPlus.isometryEquivWreath (splitOrthogonalEquiv (e g).val))).val
      (splitCoordinates (l v)) = splitCoordinates (l (ρ g v))
    rw [BinaryFourPlus.wreathToIsometry_equiv,splitOrthogonalEquiv_intertwines,he]
  have hi : ∀ x ∈ pResidual 2 BinaryFourPlus.Wreath,
      k r*x*(k r)⁻¹=x⁻¹ := by
    intro x hx
    obtain ⟨y,rfl⟩ := k.surjective x
    have hy : y ∈ pResidual 2 G := by
      have hm : k y ∈ (pResidual 2 G).map k.toMonoidHom := by
        rw [map_pResidual 2 k]
        exact hx
      obtain ⟨z,hz,hzy⟩ := hm
      exact k.injective hzy ▸ hz
    simpa only [map_mul,map_inv] using congrArg k (hinv y hy)
  exact BinaryFourPlus.residual_inverter_moves_in_coordinates f (ρ r) (k r)
    ((k.orderOf_eq r).trans hr) hi (fun v => (hact r v).symm) S hd
end CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four
