module
public import Theory.GroupTheory.FourCenterSylowPromotion
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorSupplementResidual
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.PointFiveFree
/-!
# Promoting the supplement centralizer to a global Sylow subgroup

For the actual source supplement element d, O^2(H) centralizes d, so
C_T(d) is Sylow in C_H(d). The five-free order of H separates the original
point z from any d whose centralizer contains the source A5 block.
Once Z(C_T(d))=<z,d> and d is conjugate to zd, normalizer control promotes
this local Sylow subgroup to Sylow in C_G(d).

The center and product-fusion premises are the concrete geometry still to
be supplied by the marked deleted-coordinate model. The local Sylow and
nonfusion premises are discharged here from the original source hypotheses.
Source: Aschbacher–Smith 14.3.20, second paragraph, printed pp.997–998.
-/
public section
open Subgroup

open Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
theorem source_factor_supplement_centralizer_sylow_of_four_center
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (A:Subgroup G) [IsElementaryAbelian 2 A]
    (hAR:A≤(F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hVA:rankTwoSeed T M≤A) (hAc:Nat.card A=16)
    (hc8:Nat.card (A⊓F.U:Subgroup G)=8)
    (hAN:F.I₂ (sourceResidual M Mc)⊔F.H.pCoreIn 2≤normalizer (A:Set G))
    (hlt:A<centralizer (A:Set G))
    (d : G) (hd : d ∈ F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G))
    (z : G) (hz : F.Vi 1=zpowers z) (hd2 : orderOf d=2)
    (hcenter : (center ((T : Subgroup G) ⊓ centralizer ({d} : Set G) : Subgroup G)).map
      ((T : Subgroup G) ⊓ centralizer ({d} : Set G)).subtype=closure ({z,d} : Set G))
    (hprod : IsConj d (z*d))
    (B : Subgroup G) (hB : B≤centralizer ({d} : Set G)) (hfive : 5∣Nat.card B) :
    normalizer ((T : Subgroup G) ⊓ centralizer ({d} : Set G) : Set G) ≤ F.H ∧
    ∃ S : Sylow 2 (centralizer ({d} : Set G)),
      (S : Subgroup (centralizer ({d} : Set G))).map
        (centralizer ({d} : Set G)).subtype=
          (T : Subgroup G) ⊓ centralizer ({d} : Set G) := by
  have hz2 : orderOf z=2 := by
    rw [←Nat.card_zpowers,←hz]
    simpa using F.card 1 (by decide)
  have hzmem : z∈F.Vi 1 := hz.symm ▸ mem_zpowers z
  have hz1 : z≠1 := by intro he; simp [he] at hz2
  have hnf := source_not_isConj_point_of_five_dvd_subgroup
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs z d hzmem hz1 B hB hfive
  have hH : F.H=centralizer ({z} : Set G) := F.H_eq_centralizer (by decide) z hz
  have hdH : d∈F.H := F.H.pCoreIn_le 2 hd.1
  have hzd : Commute z d :=
    (mem_centralizer_singleton_iff.mp (hH ▸ hdH)).symm
  have hN : normalizer ((T : Subgroup G) ⊓ centralizer ({d} : Set G) : Set G) ≤ F.H := by
    rw [hH]
    exact normalizer_le_centralizer_of_four_center_fusion _ z d hz2 hd2 hzd hcenter hnf hprod
  refine ⟨hN,exists_sylow_map_eq_of_local_normalizer _
    (F.H ⊓ centralizer ({d} : Set G)) (centralizer ({d} : Set G))
      T.isPGroup'.to_inf_left inf_le_right ?_ ?_⟩
  · exact source_factor_supplement_local_centralizer_sylow_of_strict_centralizer
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN hlt d hd
  · exact le_inf (inf_le_left.trans hN) inf_le_right
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
