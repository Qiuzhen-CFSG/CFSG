module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.LiteralCentralizer.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.LiteralCentralizer.SeedCentralizer
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.LiteralCentralizer.SeedWitness

/-!
# Ambient centralizer control inside literal max1

If `gsg⁻¹` belongs to `Z(O₂(A))`, every element centralizing that center is
carried by conjugation with `g⁻¹` into `C_J₄(s)`. When `g` belongs to max1
and that seed centralizer lies in max1, the original element lies there too.
The candidate's own Sylow witness supplies the local section for the seed
membership calculation.

The proved intrinsic seed witness and full ambient seed-centralizer bound
discharge both premises of the reduction below. Thus every source-local
L₄(2) section with literal max1 as a candidate satisfies
`C_J₄(Z(O₂(A))) ≤ max1`, without identifying the two Sylow witnesses or
assuming that the section is normal in max1.

Source: the auxiliary max1 geometry for Aschbacher–Smith A.3.12(17) and the
proof of 1.3.9, printed pp.47–48 and 514; GLS3 Table 5.3i.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
open Section02.LocalModels

namespace AmbientGeometry

private theorem centralizer_le_of_conjugate_mem
    {G : Type*} [Group G] (M Z : Subgroup G) (s : M)
    (hcent : centralizer ({(s : G)} : Set G) ≤ M)
    (g : M) (hg : (g : G) * s * (g : G)⁻¹ ∈ Z) :
    centralizer (Z : Set G) ≤ M := by
  intro x hx
  have hc : (s : G) * ((g : G)⁻¹ * x * g) = ((g : G)⁻¹ * x * g) * s := by
    have h := congrArg (fun y : G => (g : G)⁻¹ * y * g) (hx _ hg)
    simpa [mul_assoc] using h
  have hm : (g : G)⁻¹ * x * g ∈ M := hcent (by
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact hc)
  have h := M.mul_mem (M.mul_mem g.property hm) (M.inv_mem g.property)
  simpa [mul_assoc] using h

attribute [local irreducible] Janko4.modelGroup certifiedMathieuSubgroup

/-- A local seed conjugate in the center transfers its ambient centralizer bound. -/
theorem centralizer_coreCenter_le_of_seed_conjugate
    (hcent : LiteralSeedCentralizerBound) (A : Subgroup Janko4.Model)
    (g : certifiedMathieuSubgroup)
    (hg : (g : Janko4.Model) * literalCentralizerSeed * (g : Janko4.Model)⁻¹ ∈ coreCenter A) :
    centralizer (coreCenter A : Set Janko4.Model) ≤ certifiedMathieuSubgroup :=
  centralizer_le_of_conjugate_mem _ _ literalCentralizerSeed hcent g hg

/-- Conditional assembly from two independent concrete calculations.
Neither premise is supplied by the intrinsic self-centralizer theorem for max1. -/
theorem literalCentralizerControl_of_seed
    (hcent : LiteralSeedCentralizerBound) (hwitness : LocalCoreCenterSeedWitness) :
    LiteralCentralizerControl := by
  intro A _ hA _ hM
  obtain ⟨g, hg⟩ := exists_seed_conjugate_mem_coreCenter_of_local_witness hwitness A hA hM
  exact centralizer_coreCenter_le_of_seed_conjugate hcent A g hg

/-- The ambient centralizer of the embedded center of a local section's two-core
lies in literal max1 whenever that subgroup is a candidate for the section. -/
theorem literalCentralizerControl : LiteralCentralizerControl :=
  literalCentralizerControl_of_seed literalSeedCentralizerBound localCoreCenterSeedWitness

end AmbientGeometry
end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
