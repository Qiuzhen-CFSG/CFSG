module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.CheckedShortAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.MarkedPlane.SourceLine
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Geometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Geometry.Thompson
public import Theory.ElementaryAbelian.AbelianNormalClosure


/-!
# Original source geometry for the short-block cases

The marked seed and characteristic-two core put [V,Lᵥ] inside the genuine
short-block layer. Its order four, full movement, and Sylow invariance come
from the original A₅ module and flag. Sylow restriction then constructs every
field of the source-line record used by the binary rank-two model calculations.

The same original local configuration supplies the earlier conjugate a and its
checked Sylow-central image. Applying the checked short-block theorem gives
centralization of that exact marked a, with no supplement or marking witness.
Only the model-specific fixed-space comparison remains for a family producer.

Source: Aschbacher–Smith, 13.6.22, printed pp.932–933, with the flag on p.926.
-/

public section
open Subgroup Stellmacher
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination
open SourceSmallModels SourceSmallModels.BinaryRankTwo

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {K L M V V₁ V₂ : Subgroup G}

/-- Construct all source-line inputs from the original flag and short block. -/
theorem sourceLineData_of_localConfiguration
    (d : FlagSource T L V V₁ V₂) (c : LocalConfiguration M d.flag)
    (hshort : IsShort K)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hLK : Lv L (markedV d.flag.module) ≤ K)
    (hchar : Theory.GroupTheory.generalizedFitting (Gv (markedV d.flag.module)) =
      pCore 2 (Gv (markedV d.flag.module)))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Nonempty (SourceLineData L K V (Tv (T : Subgroup G) (markedV d.flag.module))
      (markedV d.flag.module)) := by
  let s := d.flag.module
  let T₀ := Tv (T : Subgroup G) (markedV s)
  have hSylow : CFSG.Quasithin.Chapter1.IsSylowIn 2 T₀ (Gv (markedV s)) :=
    ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩
  have hzmem := (mem_omegaOneCenterAmbient_iff (T : Subgroup G) _).mp d.flag.z_central
  have hzT : markedZ s ∈ T₀ := ⟨hzmem.1, markedZ_mem_Gv s⟩
  have hzOmega : markedZ s ∈ omegaOneCenterAmbient T₀ :=
    (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hzT, hzmem.2.1, fun t ht => hzmem.2.2 t ht.1⟩
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (Qv (markedV s))) :=
    omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 (Uv (markedZ s) (markedV s)) :=
    IsElementaryAbelian.of_le (Uv_le_coreOmega (T : Subgroup G) (markedZ s)
      (markedV s) hSylow hzOmega hchar)
  have hU : IsPGroup 2 (Uv (markedZ s) (markedV s)) :=
    IsElementaryAbelian.isPGroup 2 _
  let H := K ⊔ T₀
  let Q := Uv (markedZ s) (markedV s) ⊓ H
  have hKQ : K ≤ normalizer (Q : Set G) :=
    (le_inf (hK.1.1.trans (Gv_normalizes_Uv _ _))
      (le_sup_left.trans H.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hQK : Q ≤ normalizer (K : Set G) :=
    inf_le_right.trans (sup_le K.le_normalizer hn)
  have hzQ : zpowers (markedZ s) ≤ Q :=
    zpowers_le.mpr ⟨z_mem_Uv _ _, (show T₀ ≤ H from le_sup_right) hzT⟩
  have hline : ⁅V, Lv L (markedV s)⁆ ≤ sourceU K := by
    rw [sourceU_eq K hshort, AlternatingBranches.ExceptionalActors.moved_eq_seed_commutator s]
    exact (commutator_mono hzQ hLK).trans
      (commutator_le_core_commutator_of_mutual_normalization K Q hshort.twoPerfect
        (hU.to_le inf_le_left) hKQ hQK)
  have hL : T₀ ≤ normalizer (Lv L (markedV s) : Set G) :=
    AlternatingBranches.CoveredSix.Mv_normalizes_Lv hTL
  have hlineN : Lv L (markedV s) ⊔ T₀ ≤ normalizer
      ((⁅V, Lv L (markedV s)⁆ : Subgroup G) : Set G) := by
    refine sup_le (normalizer_commutator_ge_right _ _) ?_
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (d.T_normalizes ht.1),
      mem_normalizer_iff_map_conj_eq.mp (hL ht)]
  obtain ⟨S, hS⟩ := hSylow.restrict (show T₀ ≤ H from le_sup_right)
    (sup_le hK.1.1 inf_le_right)
  have hS' : (S : Subgroup H) = T₀.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hS, map_subgroupOf_eq_of_le (show T₀ ≤ H from le_sup_right)]
  refine ⟨{
    lv_le := hLK
    normalizes_K := hn
    normalizes_Lv := hL
    line_le := hline
    line_card := AlternatingBranches.CoveredSix.source_commutator_card s
    line_moved := AlternatingBranches.ExceptionalActors.moved_self_commutator s
    line_invariant := hlineN
    sylow := S
    sylow_eq := hS'
    three_dvd := ?_ }⟩
  rw [← c.residual_card]
  exact (pCore 2 (Lv L (markedV s))).card_quotient_dvd_card

/-- The original marked conjugate is centralized after the family fixed-space calculation. -/
theorem short_centralizes_markedA
    (d : FlagSource T L V V₁ V₂) (c : LocalConfiguration M d.flag)
    (hs : IsShort K)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hLK : Lv L (markedV d.flag.module) ≤ K)
    (hchar : Theory.GroupTheory.generalizedFitting (Gv (markedV d.flag.module)) =
      pCore 2 (Gv (markedV d.flag.module)))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hfix : ((blockU K).map K.subtype) ⊓ centralizer (Lv L (markedV d.flag.module) : Set G) =
      ((blockU K).map K.subtype) ⊓ centralizer (K : Set G)) :
    K ≤ Gv (markedA d.flag.module) := by
  obtain ⟨e⟩ := sourceLineData_of_localConfiguration d c hs hK hn hLK hchar hTL
  obtain ⟨P, hP⟩ := SourceActors.exists_source_sylow hn e.sylow e.sylow_eq
  have hP' : (P : Subgroup K).map K.subtype ≤ Tv (T : Subgroup G) (markedV d.flag.module) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [hP] at hk
    exact hk
  have hv : markedV d.flag.module ^ 2 = 1 := by
    change d.flag.module.map (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v) ^ 2 = 1
    rw [← map_pow]
    exact (congrArg d.flag.module.map
      (show (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v) ^ 2 = 1
        by decide +kernel)).trans d.flag.module.map.map_one
  have haD : ((inclusion inf_le_right c.aPoint : Gv (markedV d.flag.module)) : G) ∈
      centralizer (Lv L (markedV d.flag.module) : Set G) := by
    change (c.aPoint : G) ∈ _
    rw [c.aPoint_val]
    exact c.a_centralizes.2
  have ha : checkedQuotientMap (markedV d.flag.module) (inclusion inf_le_right c.aPoint) ∈
      centralizer (checkedImage (markedV d.flag.module)
        (Tv (T : Subgroup G) (markedV d.flag.module)) : Set (Gcheck (markedV d.flag.module))) := by
    rintro x ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (mem_center_iff.mp c.a_checked_central
      ((checkedSylowMap (T : Subgroup G) (markedV d.flag.module)).rangeRestrict ⟨y, hy⟩))
  have hc := checked_centralizes_short L K (Tv (T : Subgroup G) (markedV d.flag.module))
    (markedV d.flag.module) hK.1.1 hv hs hn c.reductions.centralizerSylow
    c.reductions.sylow_image P hP' hchar hLK hfix
    (inclusion inf_le_right c.aPoint) haD ha
  change K ≤ Gv (c.aPoint : G) at hc
  rwa [c.aPoint_val] at hc

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
