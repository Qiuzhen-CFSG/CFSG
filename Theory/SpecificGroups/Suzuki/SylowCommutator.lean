module
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting.Coordinates

/-!
# The derived subgroup of a Suzuki Sylow

Align the standard root group with the prescribed Sylow. The root-coordinate
identity identifies its derived subgroup with its center, which is exactly
its first omega subgroup. Both subgroups use the same ambient embedding.

Source: Huppert--Blackburn, Finite Groups III, XI.3.1, via the existing
root-coordinate proof in SchurFamilySplitting.Coordinates. The concrete
application is the middle-core quotient in DGS85 (12.3), printed p.180.
The parameter is nonbinary; Sz(2) is not included.
-/

public noncomputable section
open Subgroup
namespace BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G]

/-- The commutator subgroup is the literal ambient first omega. -/
theorem suzukiSylow_commutator_eq_omega {m : ℕ} (hm : 0 < m)
    (e : G ≃* SuzukiMatrixGroup m) (P : Sylow 2 G) :
    ⁅(P : Subgroup G), (P : Subgroup G)⁆ = omegaOneAmbient (P : Subgroup G) := by
  obtain ⟨f, hP, _⟩ := suzukiSylow_aligned_equiv hm e P
  rw [← hP, ← map_commutator, ← map_omegaOneAmbient_injective f.toMonoidHom f.injective]
  congr 1
  rw [← map_subtype_commutator, suzukiRootSubgroup_omega_eq_center m hm]
  congr 1
  exact SchurCover.Family.root_commutator_eq_center m hm
end BenderSuzuki.MatrixGroups
