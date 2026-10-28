module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.Contracts
public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.NonlinearMultiplicity.RootGeometry
public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.NonlinearMultiplicity.SplitMultiplicity

/-!
# The nonlinear root contribution in SU₃(5)

The canonical special-unitary root has order 125 and is extraspecial. Its
nonidentity central generator is conjugate to its square inside SU, so it
cannot belong to the ambient center. A representation with central kernel
therefore acts nontrivially on that generator. The exact extraspecial
multiplicity formula gives degree z + 20a with a positive, where z is the
dimension fixed by the literal embedded root center.

This discharges the nonlinear premise of
`root_fixed_dimension_of_root_calculations`; the independent linear-character
gap remains with its own owner. Neither absolute irreducibility nor a
splitting-field hypothesis is needed here.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
p.10; Aschbacher–Smith K.2, printed p.453.
-/

open Subgroup BenderSuzuki.MatrixGroups
open HermitianForm.OddPrimeSylow.NormalizedOuter
namespace Representation.SU3.FiveSmallModules.Degrees.RootEigenline
open NonlinearMultiplicity

universe u v

/-- The exact positive nonlinear multiplicity for the original coefficient
field and the canonical root-center inclusion. -/
public theorem root_nonlinear_multiplicity_input : RootNonlinearMultiplicityInput.{u, v} := by
  intro F _ _ J hc hconj K _ _ _ U _ _ _ τ hk
  obtain ⟨hp, hcard⟩ := specialRoot_structure (FormTransport.standardForm J) rfl hc hconj
  let : IsExtraspecial 5 (standardRoot J) := hp
  obtain ⟨z, hz, hz1, hfusion⟩ :=
    specialRoot_central_fusion (FormTransport.standardForm J) rfl hc hconj
  obtain ⟨g, hg⟩ := hfusion 2 (by decide) (by decide)
  have hne : τ (z : standardGroup J) ≠ 1 := by
    intro he
    have hcentral := mem_center_iff.mp (hk (MonoidHom.mem_ker.mpr he)) g
    have hfixed : g * (z : standardGroup J) * g⁻¹ = (z : standardGroup J) := by
      rw [hcentral, mul_inv_cancel_right]
    have hsquare : (z : standardGroup J) * (z : standardGroup J) =
        (z : standardGroup J) * 1 := by
      simpa only [pow_two, mul_one] using hg.symm.trans hfixed
    exact hz1 (Subtype.ext (mul_left_cancel hsquare))
  exact multiplicity τ (standardRoot J) hcard z hz hz1 hne g hg

end Representation.SU3.FiveSmallModules.Degrees.RootEigenline
