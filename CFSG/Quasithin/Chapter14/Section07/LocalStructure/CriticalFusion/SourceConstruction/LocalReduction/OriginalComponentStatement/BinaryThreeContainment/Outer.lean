module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BinaryThreeContainment.Parabolics
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ComponentEscapeAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.SolvableConclusion

/-!
# The original outside binary component has an outer Sylow actor

If all original Sylow actors were inner, the two solvable parabolic lifts
would both be normalized by L1T. Source 14.7.29 puts both in N_G(L),
contradicting escape of their component join. All structural input is at
the original G,T, with relative normality retained in this intermediate.
Source: Aschbacher--Smith 14.7.47, printed p.1064, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BinaryThreeContainment
universe u
variable {G : Type u} [Group G] [Finite G]

open Theory.GroupTheory
open scoped IsMulCommutative
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
variable {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

/-- Some element of the original Sylow acts outer on the actual component quotient. -/
theorem local_outside_outer_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) [C.Normal] (hC : C.IsCComponent)
    (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.PSL3Two.PSL) :
    ∃ t : I, t ∈ (T : Subgroup G).subgroupOf I ∧
      normalQuotientAction C (pCore 2 C) t ∉ MulAut.innerSubgroup (C ⧸ pCore 2 C) := by
  by_contra! hi
  let A := (F.Li L 1).subgroupOf I
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  have hAI := F.Li_one_le_of_mem_Hz hI
  let ea := subgroupOfEquivOfLe hAI
  have hp : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2 _).of_surjective
    ea.symm.toMonoidHom ea.symm.surjective
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    rw [Nat.card_congr (QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)).toEquiv]
    exact pointResidual_core_quotient_card_at h structural
  have hn : (S : Subgroup I) ≤ normalizer (A : Set I) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (T_normalizes_L₁_at h structural hx) (a : G)
  have hnot : ¬ A ≤ C := by
    intro hh
    apply hout
    have hm := map_mono (f := I.subtype) hh
    rwa [map_subgroupOf_eq_of_le hAI] at hm
  obtain ⟨D,E,hDE,hD,hE,hnD,hnE⟩ := inner_solvable_pair A C S hp hc hn hnot e hi
  have hmap : (A ⊔ (S : Subgroup I)).map I.subtype = F.Li L 1 ⊔ (T : Subgroup G) := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hAI,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hI)]
  have hle (B : Subgroup I) (hs : Group.IsSolvable B)
      (hnB : A ⊔ (S : Subgroup I) ≤ normalizer (B : Set I)) :
      B.map I.subtype ≤ normalizer (L : Set G) := by
    have hsB : Group.IsSolvable (B.map I.subtype) := by
      let := hs
      exact Group.isSolvable_of_surjective (I.subtype.subgroupMap_surjective B)
    apply WholeResidualAssembly.GuardedSource.point_normalized_solvable_le_normalizer
      d h hab structural previous faithful earlier (B.map I.subtype)
        ((map_subtype_le B).trans hI.2.1) hsB
    have hh := (map_mono (f := I.subtype) hnB).trans (B.le_normalizer_map I.subtype)
    rwa [hmap] at hh
  apply local_component_not_le_normalizer_at h structural I hI C hC
  rw [←hDE,Subgroup.map_sup]
  exact sup_le (hle D hD hnD) (hle E hE hnE)


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BinaryThreeContainment
