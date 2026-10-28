module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SourceClass
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.SylowLift
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Elementary
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Forms

/-!
# The central-quotient geometry needed by octad cubic fusion

The action in this module is conjugation on Q/Z(Q), where Q is the actual
restriction kernel. It is distinct from restriction to the octad lattice.
`OrthogonalModel` specifies a multiplicative coordinate equivalence with the
split binary space of dimension eight, compatibility with conjugation and
squares, the exact Omega image, and a two-group kernel. No cubic fusion is
included in this structural interface, and its existence is not asserted here.

Cyclic conjugacy through its two-group kernel gives an actual integral
centralizer element. Mapping that element by the original lattice restriction
supplies the required conjugator in the literal `action.range`.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.5 and §46, p.251.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction

abbrev KernelCentralQuotient := action.ker ⧸ Subgroup.center action.ker

/-- Conjugation on the actual central quotient, not the octad lattice action. -/
def kernelQuotientAction : centralizer →* MulAut KernelCentralQuotient :=
  Subgroup.normalQuotientAction action.ker (Subgroup.center action.ker)

theorem kernelQuotientAction_mk (g : centralizer) (k : action.ker) :
    kernelQuotientAction g (QuotientGroup.mk' (Subgroup.center action.ker) k) =
      QuotientGroup.mk' (Subgroup.center action.ker) (MulAut.conjNormal g k) :=
  Subgroup.normalQuotientAction_apply_mk action.ker (Subgroup.center action.ker) g k

namespace SelectedGeometry

abbrev Space := ClassicalOrthogonal.VectorD 4 (ZMod 2)

abbrev form : QuadraticForm (ZMod 2) Space := ClassicalOrthogonal.formD 4 (ZMod 2)

abbrev Orthogonal := quadraticIsometrySubgroup form

abbrev omega : Subgroup Orthogonal := ClassicalOrthogonal.elementarySubgroup form

/-- The moved space in the fixed hyperbolic coordinates. -/
def movedSpace (a : Orthogonal) : Submodule (ZMod 2) Space :=
  LinearMap.range (a.val.toLinearMap - LinearMap.id)

/-- A cubic rotation on an anisotropic plane has precisely this moved space. -/
def AnisotropicPlane (a : Orthogonal) : Prop :=
  Module.finrank (ZMod 2) (movedSpace a) = 2 ∧
    ∀ v ∈ movedSpace a, v ≠ 0 → form v ≠ 0

end SelectedGeometry

/-- Structural realization of the actual kernel quotient and its ambient action. -/
structure OrthogonalModel where
  coordinates : KernelCentralQuotient ≃* Multiplicative SelectedGeometry.Space
  orthogonalAction : centralizer →* SelectedGeometry.Orthogonal
  equivariant (g : centralizer) (k : action.ker) :
    coordinates (kernelQuotientAction g (QuotientGroup.mk' (Subgroup.center action.ker) k)) =
      Multiplicative.ofAdd ((orthogonalAction g).val
        (coordinates (QuotientGroup.mk' (Subgroup.center action.ker) k)).toAdd)
  square_zero_iff (k : action.ker) :
    SelectedGeometry.form
      (coordinates (QuotientGroup.mk' (Subgroup.center action.ker) k)).toAdd = 0 ↔ k ^ 2 = 1
  range_eq : orthogonalAction.range = SelectedGeometry.omega
  kernel_isTwoGroup : IsPGroup 2 orthogonalAction.ker

/-- The realization has exactly the kernel of conjugation on the actual Q/Z(Q). -/
theorem OrthogonalModel.ker_eq (M : OrthogonalModel) :
    M.orthogonalAction.ker = kernelQuotientAction.ker := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro hg
    apply MulEquiv.ext
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center action.ker) q
    apply M.coordinates.injective
    rw [M.equivariant, hg]
    rfl
  · intro hg
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    obtain ⟨q, hq⟩ := M.coordinates.surjective (Multiplicative.ofAdd v)
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center action.ker) q
    have he := M.equivariant g k
    rw [hg] at he
    change M.coordinates (QuotientGroup.mk' (Subgroup.center action.ker) k) =
      Multiplicative.ofAdd ((M.orthogonalAction g).val
        (M.coordinates (QuotientGroup.mk' (Subgroup.center action.ker) k)).toAdd) at he
    rw [hq] at he
    exact (congrArg Multiplicative.toAdd he).symm

/-- Conjugacy in the realized quotient image lifts to the required lattice image. -/
theorem quaternionImageFusion_of_orthogonalModel_image_fusion (M : OrthogonalModel)
    (hf : ∀ r s : centralizer, orderOf r = 3 → orderOf s = 3 →
      QuaternionCubic r → QuaternionCubic s →
      ∃ c : M.orthogonalAction.range,
        Subgroup.zpowers (M.orthogonalAction r) =
          (Subgroup.zpowers (M.orthogonalAction s)).map (MulAut.conj c.val).toMonoidHom) :
    QuaternionImageFusion := by
  intro r s hr hs hqr hqs
  obtain ⟨c, hc⟩ := cyclic_fusion_of_image_fusion M.orthogonalAction M.kernel_isTwoGroup
    hr hs (hf r s hr hs hqr hqs)
  refine ⟨action.rangeRestrict c, ?_⟩
  simpa [MonoidHom.map_zpowers, MulAut.conj_apply] using
    congrArg (Subgroup.map action) hc

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
