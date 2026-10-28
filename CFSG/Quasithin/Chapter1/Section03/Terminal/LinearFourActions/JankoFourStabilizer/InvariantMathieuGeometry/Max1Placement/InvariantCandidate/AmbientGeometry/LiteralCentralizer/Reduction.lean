module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.IntrinsicTransport

/-!+# A distinguished kernel element for ambient centralizer control

The word `(xy)^14` is an element of the literal max1 subgroup. Two separate
calculations suffice for the requested ambient bound: its centralizer in J₄
must lie in max1, and the center of a local L₄(2) section's two-core must
contain a max1 conjugate of that word. These are unproved contracts below.

The second calculation is intrinsic to max1. The candidate's own Sylow
witness supplies its inputs, and faithful embedding transports the center
back to J₄. No relation between that Sylow and the original ambient Sylow
is needed. In particular, relative subnormality is not replaced by normality
in max1.

Source motivation: Aschbacher–Smith A.3.12(17), printed pp.47–48, and the
proof of 1.3.9, p.514; GLS3 Table 5.3i. The table's 2B centralizer and
normalizer descriptions do not identify embedded subgroups in the matrix
model. `Max1Fusion.KernelOrbits` gives two nonidentity kernel orbits, so
nontriviality of the center alone does not supply the required seed orbit.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
open Section02.LocalModels

namespace AmbientGeometry

/-- The actual word `(xy)^14` in the literal ATLAS max1 subgroup. -/
@[expose] def literalCentralizerSeed : certifiedMathieuSubgroup :=
  Janko4.Cardinality.localKernelSeed Janko4.matrixA_mul_self Janko4.matrixB_pow_four

/-- The outstanding ambient calculation for this particular matrix-group element. -/
@[expose] def LiteralSeedCentralizerBound : Prop :=
  centralizer ({(literalCentralizerSeed : Janko4.Model)} : Set Janko4.Model) ≤
    certifiedMathieuSubgroup

/-- The outstanding local geometry selects the seed orbit inside the embedded
center of the section's two-core. All conjugators belong to literal max1. -/
@[expose] def LocalCoreCenterSeedWitness : Prop :=
  ∀ (B : Subgroup certifiedMathieuSubgroup) (T : Sylow 2 certifiedMathieuSubgroup),
    ClassicalGroup.IsPSL (XiQuotient B) 4 2 →
    B ∈ ChapterA.Section03.localCComponents T →
    ∃ g : certifiedMathieuSubgroup,
      g * literalCentralizerSeed * g⁻¹ ∈ coreCenter B

attribute [local irreducible] Janko4.modelGroup certifiedMathieuSubgroup

/-- Use the candidate's intrinsic Sylow witness and embed its core center into J₄.
The original ambient Sylow-local assumption is unnecessary for this transfer. -/
theorem exists_seed_conjugate_mem_coreCenter_of_local_witness
    (hwitness : LocalCoreCenterSeedWitness) (A : Subgroup Janko4.Model)
    (hA : ClassicalGroup.IsPSL (XiQuotient A) 4 2)
    (hM : certifiedMathieuSubgroup ∈ candidates A) :
    ∃ g : certifiedMathieuSubgroup,
      (g : Janko4.Model) * literalCentralizerSeed * (g : Janko4.Model)⁻¹ ∈ coreCenter A := by
  obtain ⟨hAM, _, T, hT⟩ := hM
  let B := A.subgroupOf certifiedMathieuSubgroup
  let f := (subgroupOfEquivOfLe hAM).symm
  have hB : ClassicalGroup.IsPSL (XiQuotient B) 4 2 :=
    hA.of_mulEquiv (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).symm
  obtain ⟨g, hg⟩ := hwitness B T hB hT
  refine ⟨g, ?_⟩
  have hcenter : (coreCenter B).map certifiedMathieuSubgroup.subtype = coreCenter A := by
    rw [map_coreCenter_of_injective _ _ certifiedMathieuSubgroup.subtype_injective,
      map_subgroupOf_eq_of_le hAM]
  rw [← hcenter]
  exact mem_map_of_mem certifiedMathieuSubgroup.subtype hg

end AmbientGeometry
end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
