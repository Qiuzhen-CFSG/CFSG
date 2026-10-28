module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticTitsInvariant
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientTitsOmegaMovement
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientHermitianThompsonWitness

/-!
# The original Tits component fixes its ambient omega-center

The actual outside component is normal in its join with the original Sylow.
Its original maximum elementary witness lies outside the full two-core of
that join. The literal omega-center action therefore has no movement by the
component, by the faithful Tits non-FF calculation. All subgroups remain on
the original source carrier.

Source: Aschbacher--Smith 6.1.4, printed pp.665--666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The original component centralizes the omega-center of the full two-core
of its actual join with the original Sylow. -/
theorem original_hermitian_tits_component_centralizes_omega
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (e : coreCentralQuotient K ≃* Tits.ParrottGroup) :
    ⁅omegaOneCenterAmbient ((K ⊔ (T : Subgroup G)).pCoreIn 2), K⁆ = ⊥ := by
  let J := K ⊔ (T : Subgroup G)
  let C := K.subgroupOf J
  let P := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hTK := original_hermitian_sylow_normalizes_tits_component
    h hout hm hM₁ hCM₁ hK hnot hq e
  let : C.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  have hTM₁ : (T : Subgroup G) ≤ M₁ := sylow_le_omegaCentralizer.trans hCM₁
  have hC : C.IsCComponent := hK.2.subgroupOf_of_le le_sup_left (sup_le hK.1 hTM₁)
  let ec : C ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let eqc := QuotientGroup.congr (pCore 2 C) (pCore 2 K) ec (pCore_map_iso 2 ec)
  let := hq
  have hqC : IsQuasisimple (C ⧸ pCore 2 C) := IsQuasisimple.of_mulEquiv eqc.symm
  have hgen : C ⊔ (P : Subgroup J) = ⊤ := by
    change K.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤
    rw [←subgroupOf_sup (show K ≤ J from le_sup_left) le_sup_right,subgroupOf_self]
  have hWP : omegaOneCenterAmbient (pCore 2 J) ≤ (P : Subgroup J) :=
    (fun x hx => pCore_isPGroup.le_sylow_of_normal P
      ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1)
  have hPm : (P : Subgroup J).map J.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hJ : ¬ elementaryAbelianMaxJ (P : Subgroup J) ≤ pCore 2 J := by
    intro hj
    obtain ⟨A,hA,_,hAR⟩ := original_hermitian_outside_maximum_elementary_witness
      h hout hm hnot
    have hjm := map_mono (f := J.subtype) hj
    rw [←elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,hPm] at hjm
    exact hAR ((le_sSup hA).trans hjm)
  have hc := tits_component_centralizes_omega C (P : Subgroup J) hC hqC
    P.isPGroup' hgen hWP ((coreCentralQuotientCongr ec).trans e) hJ
  have hcm := congrArg (Subgroup.map J.subtype) hc
  rw [map_commutator,←omegaOneCenterAmbient_map_injective J.subtype J.subtype_injective,
    map_subgroupOf_eq_of_le (show K ≤ J from le_sup_left),Subgroup.map_bot] at hcm
  exact hcm

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
