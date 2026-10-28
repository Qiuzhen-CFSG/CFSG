module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Inputs
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Reduction
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Passing from the recognized parabolic to the actual local embedding input

The parabolic is the product of its two-residual and the original full
Sylow subgroup. Its residual equality therefore identifies it with XT.
The proved Xi lemmas construct a Sylow three-complement and all the local
embedding hypotheses, including the residual relative to the chosen H.
The ambient Sylow subgroup restricts to every H containing XT.

Source: Aschbacher--Smith 1.3.2, pp.507--509, and 10.2.4, p.747.
The natural-module construction of `ParabolicSeedData` remains explicit.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure
open Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
  {L : Subgroup G} {z : G}

/-- The recognized source parabolic is exactly XT, with the original
ambient embeddings retained. -/
theorem ParabolicSeedData.seed_join_eq (r : ParabolicSeedData T L z) :
    centralizerSeed T L z ⊔ (T : Subgroup G) = r.parabolic := by
  have he := congrArg (map r.parabolic.subtype)
    (pResidual_sup_sylow_eq_top (T.subtype r.sylow_le))
  simpa only [Subgroup.map_sup, r.residual, Sylow.coe_subtype,
    map_subgroupOf_eq_of_le r.sylow_le, ← MonoidHom.range_eq_map, range_subtype] using he

/-- The S₃-wreath model belongs to the literal seed-Sylow join. -/
theorem ParabolicSeedData.seed_wreath (r : ParabolicSeedData T L z) :
    Nonempty (((centralizerSeed T L z ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (centralizerSeed T L z ⊔ (T : Subgroup G) : Subgroup G)) ≃*
      ParabolicWreath) := by
  rw [r.seed_join_eq]
  exact r.wreath

omit [Finite G] in
/-- Restricting the ambient Sylow supplies the full Sylow condition,
not merely the two-group condition from the intrinsic local record. -/
theorem sylowIn_overgroup {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H) :
    IsSylowIn 2 (T : Subgroup G) H := by
  refine ⟨T.subtype hTH, ?_⟩
  exact map_subgroupOf_eq_of_le hTH

/-- Construct the actual complement and every intrinsic local hypothesis
from the recognized parabolic, for any containing overgroup H. -/
theorem ParabolicSeedData.localInput (r : ParabolicSeedData T L z)
    {H : Subgroup G} (hH : centralizerSeed T L z ⊔ (T : Subgroup G) ≤ H) :
    ∃ P : Subgroup G, LocalInput 3 (T : Subgroup G) (centralizerSeed T L z) P H := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let P : Sylow 3 (centralizerSeed T L z) := Classical.arbitrary _
  have hxi : centralizerSeed T L z ∈ Xi G (T : Subgroup G) := r.residual ▸ r.xi
  have hq : XiOddQuotient 3 (XiQuotient (centralizerSeed T L z)) :=
    r.residual ▸ r.quotient
  exact ⟨(P : Subgroup (centralizerSeed T L z)).map (centralizerSeed T L z).subtype,
    localInput_of_mem_Xi hxi (sylowIn_overgroup (le_sup_right.trans hH)) hH
      (by decide) hq P⟩

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure
