module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.CubicFixedPoints
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.OrthogonalOrder

/-!
# Cubic fixed vectors in the original full orthogonal realization

Transport Sylow conjugation and the natural action through the marked group
and linear equivalences. The original Sylow three-subgroup therefore has
zero fixed space on the original representation.

Source application: Aschbacher--Smith, 14.3.18, printed pp.995--996.
-/

public section
open Subgroup Module
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Every Sylow three-subgroup fixes only zero in the full natural orthogonal action. -/
theorem sylow_three_fixed_eq_zero_of_full_orthogonal
    (ρ : Representation (ZMod 2) G V) (hρ : OrthogonalRealization ρ ⊤)
    (P : Sylow 3 G) (v : V) (hfix : ∀ a ∈ (P : Subgroup G), ρ a v=v) : v=0 := by
  obtain ⟨e,l,he⟩ := hρ
  let k : G ≃* BinaryFourPlus.Wreath :=
    ((e.trans topEquiv).trans splitOrthogonalEquiv).trans BinaryFourPlus.isometryEquivWreath
  let f := l.trans splitCoordinates
  have hact (g : G) (v : V) :
      (BinaryFourPlus.wreathToIsometry (k g)).val (f v)=f (ρ g v) := by
    change (BinaryFourPlus.wreathToIsometry
      (BinaryFourPlus.isometryEquivWreath (splitOrthogonalEquiv (e g).val))).val
      (splitCoordinates (l v))=splitCoordinates (l (ρ g v))
    rw [BinaryFourPlus.wreathToIsometry_equiv,splitOrthogonalEquiv_intertwines,he]
  let P' := P.mapSurjective (f:=k.toMonoidHom) k.surjective
  have hh : ∀ a ∈ (P' : Subgroup BinaryFourPlus.Wreath),
      (BinaryFourPlus.wreathToIsometry a).val (f v)=f v := by
    rintro a ⟨b,hb,rfl⟩
    exact (hact b v).trans (congrArg f (hfix b hb))
  apply f.injective
  rw [map_zero]
  exact BinaryFourPlus.sylow_three_fixed_eq_zero P' (f v) hh
end CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four
