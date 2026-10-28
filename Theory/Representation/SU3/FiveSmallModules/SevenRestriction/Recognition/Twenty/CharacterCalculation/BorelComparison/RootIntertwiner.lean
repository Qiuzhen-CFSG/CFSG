module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.BorelComparison.Inputs
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.BorelComparison.RootGeometry
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.BorelComparison.RootIntertwiner.Fusion

/-!
# A nonzero map between the degree-twenty root restrictions

The actual root is extraspecial of order 125, and the actual SU torus fuses
every nonidentity power of a generator of its center. The common-constituent
argument in `RootIntertwiner.Fusion` therefore gives a nonzero map between
the two root restrictions over the original coefficient field. Dimension
twenty is used only to establish that both representations are nonzero.

This discharges `TwentyRootIntertwining`, the root-map input to the Borel
comparison route for Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, pp.10–11, cited in Aschbacher–Smith K.2, printed p.453.
No ambient irreducibility, trivial SU-center action, or splitting hypothesis
is required.
-/

open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External HermitianForm.BorelTorus
open HermitianForm.OddPrimeSylow.NormalizedOuter
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.BorelComparison
open Degrees Degrees.RootEigenline Degrees.RootEigenline.NonlinearMultiplicity

universe v

private theorem center_invariants_eq_bot
    {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (P : Subgroup G)
    (hfix : invariants (ρ.comp ((center P).map P.subtype).subtype) = ⊥) :
    invariants ((ρ.comp P.subtype).comp (center P).subtype) = ⊥ := by
  apply bot_unique
  intro v hv
  have hmem : v ∈ invariants (ρ.comp ((center P).map P.subtype).subtype) := by
    rintro ⟨x, hx⟩
    obtain ⟨w, hw, rfl⟩ := hx
    exact hv ⟨w, hw⟩
  rw [hfix] at hmem
  exact hmem

/-- The root restrictions of the two degree-twenty, root-center-free SU₃(5)
modules have a nonzero intertwiner over the original coefficient field. -/
public theorem twenty_root_intertwining : TwentyRootIntertwining.{v} := by
  intro F _ _ J hc hconj K _ _ _ U W _ _ _ _ _ _ ρ σ hU hW hρ hσ
  let : Nontrivial U := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank K U)
  let : Nontrivial W := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank K W)
  obtain ⟨hp, hcard⟩ := specialRoot_structure (FormTransport.standardForm J) rfl hc hconj
  let : IsExtraspecial 5 (standardRoot J) := hp
  obtain ⟨z, hz, hz1, hfusion⟩ :=
    specialRoot_central_torus_fusion (FormTransport.standardForm J) rfl hc hconj
  refine RootIntertwiner.exists_intertwiner_of_fusion ρ σ (standardRoot J) hcard
    (center_invariants_eq_bot ρ _ hρ) (center_invariants_eq_bot σ _ hσ) z hz hz1 ?_
  intro i hi0 hi5
  obtain ⟨k, hk⟩ := hfusion i hi0 hi5
  exact ⟨hermitianTorusSU (FormTransport.standardForm J) rfl k, hk⟩

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.BorelComparison
