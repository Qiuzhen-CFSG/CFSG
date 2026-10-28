module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionOrbit
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicSolvable
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.TwoCoreCommutator
public import Theory.GroupTheory.PResidual.SupplementCommutator
public import Theory.GroupTheory.TwoCoreOddSylowSupplement

/-!
# The literal two-residual from the constructed TI seed

Set W to the H-orbit of O₂(H) ∩ V. The original Sylow normalizes V, so
[O₂(H), V] lies in W. The minimal-parabolic normal-subgroup dichotomy
then gives [O₂(H), O²(H)] ≤ W. The odd quotient places O²(H) in O₂(H)P.
The residual formula for a two-group supplement gives O²(H) ≤ PW; the
reverse containment follows from P being odd and W = [W,P].

Thus O²(H) = PW already follows from the initial seed. In particular this
source conclusion does not require the later invariant Sylow selection.
LocalConfigurationCyclicConstructionSource applies it to the constructed
seed under the original hypotheses. Final selection and noncyclic exclusion
remain with qt-d-12213-cyclic-block.
Source: Aschbacher–Smith, 12.2.22, printed p.803.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d p : ℕ} {g : G}

/-- The canonical elementary orbit already gives the exact two-residual,
before choosing an inverter-invariant odd Sylow subgroup. -/
theorem CyclicConstructionSeed.residual
    (S : CyclicConstructionSeed T L V d p H P U g)
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    (pResidual 2 H).map H.subtype =
      P ⊔ componentOrbit (H.pCoreIn 2 ⊓ V) H := by
  let W := componentOrbit (H.pCoreIn 2 ⊓ V) H
  have hPH : P ≤ H := S.overgroup ▸ le_sup_left
  have hVH : V ≤ H := D.le_sylow.trans S.hstar.1.1.2
  have hWQ : W ≤ H.pCoreIn 2 := CyclicConstructionSeed.orbit_in_core H V
  have hWH : W ≤ H := hWQ.trans (pCoreIn_le _ _)
  have hHQ : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := pCoreIn_le_sylow H (T.subtype S.hstar.1.1.2) hx
    exact hy
  let VH := V.subgroupOf H
  let PH := P.subgroupOf H
  let WH := W.subgroupOf H
  let : WH.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_componentOrbit _ _)
  have hcommV : ⁅pCore 2 H, VH⁆ ≤ WH := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le hVH]
    exact (le_inf (le_normalizer_iff_commutator_le_left.mp (hVH.trans hHQ))
      (le_normalizer_iff_commutator_le_right.mp (hQT.trans hTV))).trans (le_componentOrbit _ _)
  have hnot : ¬ VH ≤ pCore 2 H := by
    intro he
    apply A.hstar_movement H S.hstar
    have hh := map_mono (f := H.subtype) he
    rwa [map_subgroupOf_eq_of_le hVH] at hh
  have hcommK : ⁅pCore 2 H, pResidual 2 H⁆ ≤ WH :=
    ChapterB.minimalParabolic_twoCore_commutator_le (T.subtype S.hstar.1.1.2)
      (chosen_hstar_intrinsic_minimalParabolic D A S.hstar) VH WH
      (subgroupOf_mono H D.le_sylow) hnot hcommV
  have hPK : PH ≤ pResidual 2 H := odd_prime_subgroup_le_twoResidual S.odd_prime PH S.pgroup.comap_subtype
  have hcommP : ⁅pCore 2 H, PH⁆ ≤ WH := (commutator_mono le_rfl hPK).trans hcommK
  have hWK : WH ≤ pResidual 2 H := by
    have hm : ⁅WH, PH⁆ = WH := by
      apply map_injective H.subtype_injective
      rw [map_commutator, map_subgroupOf_eq_of_le hWH, map_subgroupOf_eq_of_le hPH,
        S.orbit_moved D A hTV]
    rw [← hm]
    exact (commutator_mono le_rfl hPK).trans (commutator_le_right _ _)
  have hKPQ : pResidual 2 H ≤ pCore 2 H ⊔ PH := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hm : (pResidual 2 H).map q ≤ PH.map q := by
      rw [S.quotient_core]
      exact (map_pResidual_le 2 q).trans
        ((pResidual_le_iff_isPGroup_quotient 2 _).mpr S.quotient_two)
    have he := map_le_iff_le_comap.mp hm
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', sup_comm] using he
  have hPperfect : IsPPerfect 2 PH := by
    apply (pResidual_eq_top_iff 2 PH).mp
    exact top_unique (odd_prime_subgroup_le_twoResidual S.odd_prime ⊤
      (S.pgroup.comap_subtype.to_subgroup ⊤))
  have hKimage : (pResidual 2 (pResidual 2 H)).map (pResidual 2 H).subtype = pResidual 2 H := by
    rw [(pResidual_eq_top_iff 2 (pResidual 2 H)).mpr (isPPerfect_pResidual 2),
      ← MonoidHom.range_eq_map, range_subtype]
  have hKPcomm : pResidual 2 H ≤ PH ⊔ ⁅pCore 2 H, PH⁆ := by
    rw [← embedded_pResidual_sup_eq_sup_commutator (pCore 2 H) PH pCore_isPGroup hPperfect,
      ← hKimage]
    exact embedded_pResidual_mono 2 hKPQ
  have hres : pResidual 2 H = PH ⊔ WH :=
    le_antisymm (hKPcomm.trans (sup_le_sup_left hcommP PH)) (sup_le hPK hWK)
  rw [hres, Subgroup.map_sup, map_subgroupOf_eq_of_le hPH, map_subgroupOf_eq_of_le hWH]

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
