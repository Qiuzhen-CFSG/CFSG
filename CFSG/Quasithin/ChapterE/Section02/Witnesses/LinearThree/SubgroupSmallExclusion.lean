module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearThree.BinarySmallExclusion
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SmallSubgroupSource
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Restricting the binary linear-three exclusion to a literal subgroup

The original small conjugation action restricts to U ∩ L with its exact
centralizer kernel and a cubic ratio at least as large. The chosen Sylow
intersection places V inside the local maximal subgroup. Containment of
that maximal in the original maximal restricts both its two-core and its
two-residual, supplying the local core and centralization hypotheses.
Containing the ambient two-core also transfers the generalized-Fitting
hypothesis. The original binary linear-three exclusion then applies in L.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.2.17,
printed p.230, applied to the actual normal-component local subgroup in
the paired PSL₂(7) branch. The local component and maximal placement remain
explicit geometric inputs; all action and source inheritance is proved here.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.LinearThree
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]

/-- Apply the original binary exclusion inside L using the restricted ambient action. -/
theorem source_subgroup_binary_small_automizer_false
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (U : Subgroup H) (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU f hf hk))
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H))
    (L : Subgroup H) (hVL : V ≤ L) (hQL : pCore 2 H ≤ L)
    (S : Sylow 2 L) (hS : (S : Subgroup L) = (T : Subgroup H).subgroupOf L)
    (hPS : ChapterB.IsMinimalParabolicOver S ⊤) (hsL : ¬ Group.IsSolvable L)
    (K : Subgroup L) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (S : Subgroup L) = ⊤)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hPS))) 3 2)
    (hML : (ChapterB.minimalParabolicMax S hPS).map L.subtype ≤
      ChapterB.minimalParabolicMax T hP)
    (houtL : ¬ V.subgroupOf L ≤ ChapterB.minimalParabolicCore S hPS) : False := by
  let : IsElementaryAbelian 2 (V.subgroupOf L) := IsElementaryAbelian.subgroupOf hVL
  let M₀ := ChapterB.minimalParabolicMax S hPS
  have hVS : V.subgroupOf L ≤ S := by
    rw [hS]
    exact comap_mono hVT
  have hTV := (normal_subgroupOf_iff_le_normalizer hVT).mp hvn
  have hSn : (S : Subgroup L) ≤ normalizer (V.subgroupOf L : Set L) := by
    rw [hS,←subgroupOf_normalizer_eq hVL]
    exact comap_mono hTV
  have hVn : ((V.subgroupOf L).subgroupOf (S : Subgroup L)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hVS).mpr hSn
  have hSU : (S : Subgroup L) ≤ U.subgroupOf L := by
    rw [hS]
    exact comap_mono hTU
  have hVM : V.subgroupOf L ≤ M₀ := hVS.trans (ChapterB.minimalParabolicMax_spec S hPS).2
  have hcore₀ : V.subgroupOf L ≤ M₀.pCoreIn 2 := by
    apply (map_le_map_iff_of_injective L.subtype_injective).mp
    rw [map_pCoreIn_of_injective 2 M₀ L.subtype L.subtype_injective]
    apply (le_inf (map_mono hVM) ?_).trans (inf_pCoreIn_le_of_le 2 hML)
    rw [map_subgroupOf_eq_of_le hVL]
    exact hcore
  have hres₀ : (pResidual 2 M₀).map M₀.subtype ≤
      centralizer (V.subgroupOf L : Set L) := by
    have he : ((pResidual 2 M₀).map M₀.subtype).map L.subtype ≤
        centralizer (V : Set H) := by
      rw [map_embedded_pResidual]
      exact (embedded_pResidual_mono 2 hML).trans hres
    intro x hx y hy
    exact Subtype.ext (he (mem_map_of_mem L.subtype hx) y hy)
  obtain ⟨hn,D₀,f₀,hf₀,hk₀,hle⟩ :=
    BenderPlacement.subgroup_small_action L hVL hU f hf hk
  have hD₀ : Nat.card D₀ ≤ 4 :=
    (Nat.card_le_card_of_injective D₀.subtype D₀.subtype_injective).trans hD
  have hV₀ : Nat.card (V.subgroupOf L) = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv).trans hV
  exact source_binary_small_automizer_false S hPS hsL K hK hgen hm
    (V.subgroupOf L) hVS hVn hcore₀ houtL
    (generalizedFitting_eq_pCore_of_normalized_by_pCore L hfit (hQL.trans L.le_normalizer))
    hV₀ (U.subgroupOf L) hSU hn f₀ hf₀ hk₀ hD₀ (lt_of_lt_of_le hratio hle) hres₀
end CFSG.Quasithin.ChapterE.Witnesses.LinearThree
