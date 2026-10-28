module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.GeometryInterface
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.KernelModel
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Counting
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Transporting the actual octad central-quotient action

Square-compatible coordinates on Q/Z(Q) determine its conjugation action in
the split binary orthogonal group. Every additive map over the prime field is
linear, and a binary quadratic form is determined by its zero set, so the square
test proves preservation of the form. The action and equivariance are constructed
from the literal quotient map, rather than supplied as further hypotheses.

For extraspecial Q the kernel of the quotient action is exactly Q C_H(Q).
Consequently a two-group bound on the actual relative centralizer suffices for
the required kernel clause. Neither existence of square-compatible coordinates
nor the exact Omega image nor that centralizer bound is asserted here.

Source: Aschbacher, *Sporadic Groups* (1994), 8.3, 25.1–25.5 and 46.1,
especially pp.132–134 and 251.
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
namespace Realization

/-- Split coordinates for the square map on the literal central quotient. -/
structure SquareCoordinates where
  coordinates : KernelCentralQuotient ≃* Multiplicative SelectedGeometry.Space
  square_zero_iff (k : action.ker) :
    SelectedGeometry.form
      (coordinates (QuotientGroup.mk' (Subgroup.center action.ker) k)).toAdd = 0 ↔ k ^ 2 = 1

namespace SquareCoordinates

variable (C : SquareCoordinates)

/-- Conjugation transported through the multiplicative quotient coordinates. -/
def additiveAction (g : centralizer) : SelectedGeometry.Space ≃+ SelectedGeometry.Space :=
  AddEquiv.toMultiplicative.symm (MulAut.congr C.coordinates (kernelQuotientAction g))

/-- The transported additive action is linear over the binary prime field. -/
def linearAction : centralizer →* (SelectedGeometry.Space ≃ₗ[ZMod 2] SelectedGeometry.Space) where
  toFun g := { C.additiveAction g with map_smul' := ZMod.map_smul (C.additiveAction g) }
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change (C.coordinates (kernelQuotientAction 1
      (C.coordinates.symm (Multiplicative.ofAdd v)))).toAdd = v
    rw [map_one]
    exact congrArg Multiplicative.toAdd (C.coordinates.apply_symm_apply _)
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    change (C.coordinates (kernelQuotientAction (g * h)
      (C.coordinates.symm (Multiplicative.ofAdd v)))).toAdd =
      (C.coordinates (kernelQuotientAction g
        (C.coordinates.symm (C.coordinates (kernelQuotientAction h
          (C.coordinates.symm (Multiplicative.ofAdd v))))))).toAdd
    rw [MulEquiv.symm_apply_apply, map_mul]
    rfl

theorem equivariant (g : centralizer) (q : KernelCentralQuotient) :
    C.coordinates (kernelQuotientAction g q) =
      Multiplicative.ofAdd (C.linearAction g (C.coordinates q).toAdd) := by
  change C.coordinates (kernelQuotientAction g q) =
    C.coordinates (kernelQuotientAction g (C.coordinates.symm (C.coordinates q)))
  rw [MulEquiv.symm_apply_apply]

/-- The square test forces every ambient actor to preserve the quadratic form. -/
theorem linearAction_preserves_form (g : centralizer) (v : SelectedGeometry.Space) :
    SelectedGeometry.form (C.linearAction g v) = SelectedGeometry.form v := by
  obtain ⟨q, hq⟩ := C.coordinates.surjective (Multiplicative.ofAdd v)
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center action.ker) q
  have he := C.equivariant g (QuotientGroup.mk' (Subgroup.center action.ker) k)
  rw [kernelQuotientAction_mk, hq] at he
  have he' : (C.coordinates (QuotientGroup.mk' (Subgroup.center action.ker)
      (MulAut.conjNormal g k))).toAdd = C.linearAction g v :=
    congrArg Multiplicative.toAdd he
  have hz : SelectedGeometry.form (C.linearAction g v) = 0 ↔
      SelectedGeometry.form v = 0 := by
    rw [← he', C.square_zero_iff]
    have hv := C.square_zero_iff k
    rw [hq] at hv
    change SelectedGeometry.form v = 0 ↔ k ^ 2 = 1 at hv
    rw [hv, ← map_pow, ← (MulAut.conjNormal g).map_one,
      (MulAut.conjNormal g).injective.eq_iff]
    rw [map_one]
  have binary : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide
  exact binary _ _ hz

/-- The orthogonal action determined by the given square coordinates. -/
def orthogonalAction : centralizer →* SelectedGeometry.Orthogonal :=
  (C.linearAction).codRestrict (quadraticIsometrySubgroup SelectedGeometry.form)
    (fun g => (mem_quadraticIsometrySubgroup _ _).mpr (C.linearAction_preserves_form g))

theorem orthogonalAction_equivariant (g : centralizer) (k : action.ker) :
    C.coordinates (kernelQuotientAction g (QuotientGroup.mk' (Subgroup.center action.ker) k)) =
      Multiplicative.ofAdd ((C.orthogonalAction g).val
        (C.coordinates (QuotientGroup.mk' (Subgroup.center action.ker) k)).toAdd) :=
  C.equivariant g _

/-- Coordinate transport does not change the intrinsic conjugation kernel. -/
theorem orthogonalAction_ker :
    C.orthogonalAction.ker = kernelQuotientAction.ker := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro hg
    apply MulEquiv.ext
    intro q
    apply C.coordinates.injective
    have he := C.equivariant g q
    have hl : C.linearAction g = 1 := congrArg Subtype.val hg
    rw [hl] at he
    exact he
  · intro hg
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    obtain ⟨q, hq⟩ := C.coordinates.surjective (Multiplicative.ofAdd v)
    have he := C.equivariant g q
    rw [hg] at he
    change C.coordinates q = Multiplicative.ofAdd (C.linearAction g (C.coordinates q).toAdd) at he
    rw [hq] at he
    exact (congrArg Multiplicative.toAdd he).symm

end SquareCoordinates

/-- Trivial action on Q/Z(Q) means inner action on Q. -/
theorem kernelQuotientAction_ker_eq (hExtra : IsExtraspecial 2 action.ker) :
    kernelQuotientAction.ker =
      action.ker ⊔ Subgroup.centralizer (action.ker : Set centralizer) := by
  let := hExtra
  have heq : kernelQuotientAction =
      (Subgroup.quotientAut (Subgroup.center action.ker)).comp
        (MulAut.conjNormal : centralizer →* MulAut action.ker) := by
    apply MonoidHom.ext
    intro g
    apply MulEquiv.ext
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center action.ker) q
    rw [kernelQuotientAction_mk]
    exact (Subgroup.quotientAut_apply_mk _ _ _).symm
  rw [heq, ← MonoidHom.comap_ker,
    IsExtraspecial.quotientAut_center_ker_eq_range_conj (p := 2)]
  exact MulAut.conjNormal_comap_innerSubgroup action.ker

/-- A two-group relative centralizer gives the required two-group action kernel. -/
theorem kernelQuotientAction_isTwoGroup_of_centralizer
    (hExtra : IsExtraspecial 2 action.ker)
    (hc : IsPGroup 2 (Subgroup.centralizer (action.ker : Set centralizer))) :
    IsPGroup 2 kernelQuotientAction.ker := by
  rw [kernelQuotientAction_ker_eq hExtra]
  exact kernel_isTwoGroup.to_sup_of_normal_left hc

/-- Assembly using the exact range and intrinsic kernel as explicit inputs. -/
def SquareCoordinates.toOrthogonalModel (C : SquareCoordinates)
    (hRange : C.orthogonalAction.range = SelectedGeometry.omega)
    (hKernel : IsPGroup 2 kernelQuotientAction.ker) : OrthogonalModel where
  coordinates := C.coordinates
  orthogonalAction := C.orthogonalAction
  equivariant := C.orthogonalAction_equivariant
  square_zero_iff := C.square_zero_iff
  range_eq := hRange
  kernel_isTwoGroup := by rw [C.orthogonalAction_ker]; exact hKernel

end Realization
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction

