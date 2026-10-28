module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Rigidity.PairedAction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Rigidity.Pairing.DifferenceGeometry

/-!
# A nondegenerate binary pairing on the literal fixed space

Use a linear section of the actual difference operator to descend the ambient
Leech polar form. Its characterization
`β(v, (u - 1)z) = leechPolar v z` removes dependence on that section and proves
symmetry, nondegeneracy, and invariance under the full reference centralizer.
The tetrahedral intertwining identity makes the actual scalar Y self-adjoint
for this pairing. `Pairing.ScalarExtension` recovers the required F-valued form.

Source context: Aschbacher, *Sporadic Groups* (1994), 49.2, p.280, and 49.5,
p.283. This is a direct construction from the attributed ATLAS Leech polar
form, not its degenerate restriction to the fixed space.
-/

public noncomputable section
open Atlas.Conway Atlas.Algebra Atlas.Codes Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
namespace PairingBinary
open PairingGeometry
open scoped Long

private theorem polar_invariant (g : LeechCentralQuotient) (v w : LeechModTwo) :
    leechPolar (rho g v) (rho g w) = leechPolar v w := by
  obtain ⟨h, rfl⟩ := leechCentralProjection_surjective g
  exact leechModTwoRepresentation_polar h v w

private theorem polar_move (g : LeechCentralQuotient) (v w : LeechModTwo) :
    leechPolar (rho g v) w = leechPolar v (rho g⁻¹ w) := by
  have h := polar_invariant g v (rho g⁻¹ w)
  simpa only [map_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using h

private theorem difference_adjoint (v w : LeechModTwo) :
    leechPolar (difference u v) w = leechPolar v (difference u w) := by
  change leechPolarBilin (rho u v - v) w = leechPolarBilin v (rho u w - w)
  rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right]
  congr 1
  exact (polar_move u v w).trans (by rw [inv_eq_of_mul_eq_one_left u_sq]; rfl)

/-- The actual difference operator, with its full image identified with the fixed space. -/
def toFixed : LeechModTwo →ₗ[Bit] fixedSpace :=
  (difference u).codRestrict fixedSpace (fun v => range_eq_fixedSpace ▸ ⟨v, rfl⟩)

theorem toFixed_surjective : Function.Surjective toFixed := by
  intro v
  have hv : v.val ∈ LinearMap.range (difference u) := range_eq_fixedSpace.symm ▸ v.property
  obtain ⟨w, hw⟩ := hv
  exact ⟨w, Subtype.ext hw⟩

private def sectionMap : fixedSpace →ₗ[Bit] LeechModTwo :=
  Classical.choose (toFixed.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr toFixed_surjective))

private theorem sectionMap_spec (v : fixedSpace) : toFixed (sectionMap v) = v :=
  LinearMap.congr_fun (Classical.choose_spec
    (toFixed.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr toFixed_surjective))) v

private theorem difference_section (v : fixedSpace) : difference u (sectionMap v) = v.val :=
  congrArg Subtype.val (sectionMap_spec v)

/-- Descent of the ambient polar form through the square-zero difference operator. -/
def form : LinearMap.BilinForm Bit fixedSpace :=
  leechPolarBilin.compl₁₂ sectionMap fixedSpace.subtype

theorem form_right_difference (v : fixedSpace) (z : LeechModTwo) :
    form v (toFixed z) = leechPolar v.val z := by
  change leechPolar (sectionMap v) (difference u z) = leechPolar v.val z
  rw [← difference_adjoint, difference_section]

theorem form_symm (v w : fixedSpace) : form v w = form w v := by
  calc
    form v w = form v (toFixed (sectionMap w)) := by rw [sectionMap_spec]
    _ = leechPolar v.val (sectionMap w) := form_right_difference _ _
    _ = form w v := leechPolar_comm _ _

theorem form_left_difference (z : LeechModTwo) (w : fixedSpace) :
    form (toFixed z) w = leechPolar z w.val := by
  rw [form_symm, form_right_difference, leechPolar_comm]

theorem form_nondegenerate : form.Nondegenerate := by
  constructor
  · intro v hv
    apply Subtype.ext
    apply leechPolar_nondegenerate
    intro z
    exact (form_right_difference v z).symm.trans (hv (toFixed z))
  · intro w hw
    apply Subtype.ext
    apply leechPolar_nondegenerate
    intro z
    exact (form_right_difference w z).symm.trans
      ((form_symm w (toFixed z)).trans (hw (toFixed z)))

private theorem toFixed_y (z : LeechModTwo) :
    Long.yEnd (toFixed z) = toFixed (rho y⁻¹ z) := by
  apply Subtype.ext
  exact intertwine z

/-- Balancing uses the literal scalar Y and the proved tetrahedral intertwining identity. -/
theorem form_balanced (v w : fixedSpace) : form (Long.yEnd v) w = form v (Long.yEnd w) := by
  obtain ⟨z, rfl⟩ := toFixed_surjective w
  rw [toFixed_y, form_right_difference, form_right_difference]
  exact polar_move y v.val z

private theorem toFixed_action (g : referenceCentralizer) (z : LeechModTwo) :
    referenceFixedAction g (toFixed z) = toFixed (rho g.val z) := by
  apply Subtype.ext
  change rho g.val (rho u z - z) = rho u (rho g.val z) - rho g.val z
  rw [map_sub]
  congr 1
  have h := g.property.1 u (U_le_I u_mem)
  simpa only [map_mul, LinearEquiv.mul_apply] using
    congrArg (fun k => rho k z) h.symm

/-- The descended form is invariant under the full ambient common centralizer. -/
theorem form_invariant (g : referenceCentralizer) (v w : fixedSpace) :
    form (referenceFixedAction g v) (referenceFixedAction g w) = form v w := by
  obtain ⟨z, rfl⟩ := toFixed_surjective w
  rw [toFixed_action, form_right_difference, form_right_difference]
  exact polar_invariant g.val v.val z

end PairingBinary

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
