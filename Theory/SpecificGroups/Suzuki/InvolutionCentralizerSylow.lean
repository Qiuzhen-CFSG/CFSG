module
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry

/-!
# Suzuki involution centralizers as prescribed Sylow subgroups

A two-group centralizer is contained in a Sylow subgroup. Since square-one
members of a Suzuki Sylow are central, that entire Sylow centralizes the
original involution. Thus the given centralizer is itself Sylow, preserving
the literal element and subgroup. This supports the marked intersection in
Aschbacher--Smith E.2.7, printed p.221.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G]
theorem suzuki_sylow_of_involution_centralizer {m : ℕ} (hm : 0<m)
    (e : G ≃* SuzukiMatrixGroup m) (z : G) (hz : z^2=1)
    (hc : IsPGroup 2 (centralizer ({z} : Set G))) :
    ∃ S : Sylow 2 G, (S : Subgroup G)=centralizer ({z} : Set G) := by
  obtain ⟨S,hS⟩ := hc.exists_le_sylow
  have hzS : z ∈ (S : Subgroup G) := hS (mem_centralizer_singleton_iff.mpr rfl)
  have hzO : z ∈ omegaOneAmbient (S : Subgroup G) :=
    (omegaOneAmbient_le_iff _ _).mp le_rfl z hzS hz
  rw [suzukiSylow_omega_eq_center hm e S] at hzO
  obtain ⟨u,hu,he⟩ := hzO
  refine ⟨S,le_antisymm ?_ hS⟩
  intro x hx
  apply mem_centralizer_singleton_iff.mpr
  rw [←he]
  exact congrArg (fun a : S => (a:G)) (mem_center_iff.mp hu ⟨x,hx⟩)
end BenderSuzuki.MatrixGroups
