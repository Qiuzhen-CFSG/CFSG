module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableNormalized
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# The three-core preimage in the original normalizer

A normal solvable subgroup of I/O₂(I) has solvable full preimage, since
the quotient kernel is a two-group. Source 14.7.29 therefore puts that
preimage in M and shows that it normalizes the literal point residual.
Apply this to O₃(I/O₂(I)) and transport normalization through the same
quotient map. No cyclicity, point normality in I, or odd-core equality
is assumed or concluded here.

Source: Aschbacher–Smith, 14.7.27–29, printed pp.1054–1055,
refs/quasithin.pdf. These are preparatory containments for the three-core
bound, using the already proved 14.7.29 by an independent route.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Pull a normal solvable subgroup of the literal star quotient back through
its full two-core. Its ambient lift lies in M and normalizes the actual L₁. -/
theorem local_normal_solvable_star_preimage_control
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (N : Subgroup (HStar I)) [N.Normal] (hs : Group.IsSolvable N) :
    let W := (N.comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
    W ≤ normalizer (L : Set G) ∧ W ≤ normalizer (F.Li L 1 : Set G) := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := N.comap q
  let := hs
  let : Group.IsNilpotent q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.isNilpotent
  have hBs : Group.IsSolvable B := isSolvable_comap_of_solvable_ker q N
  have hIN : I ≤ normalizer (B.map I.subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      B.le_normalizer_map I.subtype
  have hBsn : Group.IsSolvable (B.map I.subtype) := by
    let := hBs
    exact Group.isSolvable_of_surjective (f := I.subtype.subgroupMap B)
      (I.subtype.subgroupMap_surjective B)
  refine ⟨local_normal_solvable_le_normalizer d h hab structural previous faithful earlier
    I hI B hBs, ?_⟩
  exact point_normalized_solvable_normalizes_point d h hab structural previous faithful earlier
    (B.map I.subtype) ((map_subtype_le B).trans hI.2.1) hBsn
    ((sup_le (F.Li_one_le_of_mem_Hz hI) (F.sylow_le_of_mem_Hz hI)).trans hIN)

/-- In every original local, the full preimage of O₃(I*) is contained
in M and normalizes L₁. This keeps the actual quotient map and its entire
kernel, rather than replacing the preimage by a chosen Sylow subgroup. -/
theorem local_threeCore_preimage_control
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    let W := ((pCore 3 (HStar I)).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
    W ≤ normalizer (L : Set G) ∧ W ≤ normalizer (F.Li L 1 : Set G) := by
  let : Group.IsNilpotent (pCore 3 (HStar I)) := pCore_isPGroup.isNilpotent
  exact local_normal_solvable_star_preimage_control d h hab structural previous faithful earlier
    I hI (pCore 3 (HStar I)) inferInstance

/-- The same three-core normalizes the literal point image in I/O₂(I).
This does not assert that the point is normal in the whole local. -/
theorem local_threeCore_normalizes_point_star
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    pCore 3 (HStar I) ≤ normalizer
      (((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) : Set (HStar I)) := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := (pCore 3 (HStar I)).comap q
  have hn := (local_threeCore_preimage_control d h hab structural previous faithful earlier I hI).2
  have hnI : B ≤ normalizer ((F.Li L 1).subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq (F.Li_one_le_of_mem_Hz hI)]
    intro b hb
    exact hn (mem_map_of_mem I.subtype hb)
  have hm := (map_mono (f := q) hnI).trans (le_normalizer_map q)
  rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hm

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
