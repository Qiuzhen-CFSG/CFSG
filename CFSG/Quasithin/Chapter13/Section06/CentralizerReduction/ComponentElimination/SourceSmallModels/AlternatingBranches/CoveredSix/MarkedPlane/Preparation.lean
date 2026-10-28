module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.MarkedPlane.QuotientComparison
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport

/-!
# Preparing the source covered-six quotient comparison

The exceptional block is short intrinsically. The genuine Tᵥ-invariance
makes it normal, hence a block, inside KTᵥ; no ambient-G subnormality is
asserted. The seed z belongs to Tᵥ, so W_K is contained in KTᵥ. Its
normality and the earlier two-group property of Uᵥ place W_K in the
specified Sylow Tᵥ. These are exactly the two application premises of the
literal core-to-plus comparison.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.926–932, especially 13.6.14 and the block paragraph of 13.6.22.
-/

public section
open Subgroup CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction ComponentSelection
variable {G : Type*} [Group G] [Finite G]

/-- The block is relative to KTᵥ, where it is actually normal. -/
theorem relative_block_of_invariant (K T : Subgroup G) (v : G)
    (h : IsExceptionalAhat6Block K)
    (hn : Tv T v ≤ normalizer (K : Set G)) :
    IsBlock (K.subgroupOf (K ⊔ Tv T v)) := by
  have hN : (K.subgroupOf (K ⊔ Tv T v)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hn)
  exact ⟨inferInstance, h.1.of_mulEquiv (subgroupOfEquivOfLe le_sup_left).symm,
    hN.isSubnormal⟩

omit [Finite G] in
/-- The literal plus module lies in the original local Sylow subgroup. -/
theorem WK_le_Tv_of_source (K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hzT : z ∈ Tv T v) (hU : IsPGroup 2 (Uv z v)) :
    WK K L T z v ≤ Tv T v := by
  let H := K ⊔ Tv T v
  have ha : plusActor K L T v = H := by
    rw [plusActor, Kminus_eq_of_invariant K T v hn, sup_of_le_left hLK]
  have hWH : WK K L T z v ≤ H :=
    conjugateSpanBy_le (zpowers_le.mpr ((show Tv T v ≤ H from le_sup_right) hzT))
      (by rw [Kminus_eq_of_invariant K T v hn];
          exact (sup_le le_sup_left (hLK.trans le_sup_left)).trans H.le_normalizer)
  have hN : ((WK K L T z v).subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (ha ▸ plusActor_normalizes_WK K L T z v hL hz)
  have hp : IsPGroup 2 ((WK K L T z v).subgroupOf H) :=
    (hU.to_le (WK_le_Uv K L T z v hK.1.1)).comap_subtype
  obtain ⟨P, hP⟩ := hK.1.2.2.1
  intro w hw
  rw [← hP]
  exact mem_map.mpr ⟨⟨w, hWH hw⟩, hp.le_sylow_of_normal P hw, rfl⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
