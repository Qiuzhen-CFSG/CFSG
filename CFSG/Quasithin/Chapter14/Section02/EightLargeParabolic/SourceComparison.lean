module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.CatalogueSelection
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceReducedPair
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FullGeometry

/-!
# Exhaustive comparison on the original normal L₂(8) source pair

The original source hypotheses give full-overlap degrees nine and three,
the odd factor seven, and core quotient orders 504 and 42. These exclude
every other concrete catalogue row and fix the binary triality parameter
and orientation. The resulting isomorphism retains the original H, the
whole second parabolic YT(M ∩ O²(H)), and both inclusion squares.

The existing order and endpoint consumers apply to this same marking.
The exhaustive comparison itself remains the earlier DGS assembly input;
this module does not assert that classification premise unconditionally.
Source: Aschbacher–Smith 14.2.16(1), pp.986–987; F.1.12, pp.262–264;
DGS (1985), Part II, Theorem A and (15.1)–(15.3), pp.99–100,225–231.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
  (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
  (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
  {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
  (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  (hcard : Nat.card (localModule T M) = 4)
  (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
  (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
  (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR

/-- Exhaustive selection at the unchanged original source prefix. The input
is the entire concrete catalogue, not a selected triality alternative. -/
theorem source_markedTriality_of_comparison
    (hc : Chapter6.Source.RankOneGeneric.Global.ConcreteAmalgamComparison
      (amalgam T M Mc H)) : Nonempty (MarkedTriality T M Mc H) := by
  let P := secondParabolic T M Mc H
  let B := H ⊓ P
  obtain ⟨h0,h1,hB,hI,hPM⟩ := source_parabolics
    hG T hempty hM hu hmany hcard e H hH eR
  obtain ⟨hiL,hiR⟩ := source_local_degrees hG T hempty hM hu hmany hcard e H hH eR
  have hTB : (T : Subgroup G) ≤ B := by
    rw [show B = H ⊓ M from hI]
    exact le_inf hH.1.1.2 hM.1.2
  have hcardIndex (A D : Subgroup G) (hle : A ≤ D) :
      Nat.card D = Nat.card A * A.relIndex D := by
    have hh := (A.subgroupOf D).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at hh
    exact hh.symm
  have hBL : Nat.card H = Nat.card B * 9 := by
    rw [hcardIndex B H inf_le_left, show B = H ⊓ M from hI, hiL]
  have hBR : Nat.card P = Nat.card B * 3 := by
    rw [hcardIndex B P inf_le_right, show B = H ⊓ M from hI, hiR]
  have hiT : (T : Subgroup G).relIndex B = 7 := by
    rw [show B = H ⊓ M from hI]
    exact source_sylow_index_borel hG T hempty hM hu hmany hcard e H hH eR
  have h7 : 7 ∣ Nat.card B := by
    rw [hcardIndex (T : Subgroup G) B hTB, hiT]
    exact dvd_mul_left _ _
  have hQL : Nat.card (H ⧸ pCore 2 H) = 504 := by
    rw [Nat.card_congr
      (sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR).toEquiv,
      ← Nat.card_congr (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).toEquiv,
      GorensteinWalter.sl2_card_formula, GaloisField.card 2 3 (by decide)]
    norm_num
  have hQR : Nat.card (P ⧸ pCore 2 P) = 42 := by
    have hF := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1
    have hQT : P.pCoreIn 2 ≤ (T : Subgroup G) := by
      have hh := hF.parabolic_core_le_S 1
      rwa [h1] at hh
    have hiQ := (source_core_indices hG T hempty hM hu hmany hcard e H hH eR).2
    have hiTP : (T : Subgroup G).relIndex P = 21 := by
      rw [← relIndex_mul_relIndex (T : Subgroup G) B P hTB inf_le_right, hiT,
        show B = H ⊓ M from hI, hiR]
    have hiQP : (P.pCoreIn 2).relIndex P = 42 := by
      rw [← relIndex_mul_relIndex (P.pCoreIn 2) (T : Subgroup G) P hQT
        (hTB.trans inf_le_right), hiQ, hiTP]
    have he : (P.pCoreIn 2).subgroupOf P = pCore 2 P :=
      Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
    change ((P.pCoreIn 2).subgroupOf P).index = 42 at hiQP
    rwa [he, index_eq_card] at hiQP
  exact Catalogue.triality_of_comparison hBL hBR h7 hQL hQR hc

/-- Apply the selected original marking to the established geometric consumer.
No new order, completion, or endpoint-equality premise is assumed. -/
theorem source_geometry_of_comparison
    (hc : Chapter6.Source.RankOneGeneric.Global.ConcreteAmalgamComparison
      (amalgam T M Mc H)) :
    Nat.card T = 4096 ∧ Nat.card (H.pCoreIn 2) = 512 ∧
      Nat.card ((secondParabolic T M Mc H).pCoreIn 2) = 2048 ∧
      Mc = H ∧ secondParabolic T M Mc H = M := by
  obtain ⟨r⟩ := source_markedTriality_of_comparison hG T hempty hM hu hmany hcard e H hH eR hc
  exact ⟨source_sylow_card r hH.1.1.2, firstCore_card r, secondCore_card r,
    source_endpoints_eq hG hempty hM hu hmany hcard e hH r⟩

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
