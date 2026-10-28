module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.ResidualControl
public import Theory.GroupTheory.TwoLocalUniquenessControl.NormalSubgroups
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow

/-!
# Normalizer control for the Case-I residual

The source uniqueness subgroup M_ZT has characteristic two because its
nontrivial normal two-subgroup Q₁ lies in its two-core. The residual
Y=O²(M_Z) is nontrivial: otherwise M_Z is a two-group and the literal
Sylow restriction puts M_Z inside T, contradicting the multiple maximal
local overgroups of T. Since M_ZT normalizes Y, characteristic-two
inheritance gives a nontrivial two-core in Y. Uniqueness therefore controls
its full ambient normalizer.

This discharges the residual-normalizer input used to construct the
outside component in source15.1.19(6); no component is assumed here.
Source: Aschbacher--Smith15.1.18(7) and the proof of15.1.19(2), p.1093.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterB Chapter14.SourcePreliminaries Chapter12.Section08
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
namespace CaseIMarkedSubgroup
variable {T : Sylow 2 G} {M Mc V Z1 : Subgroup G}
local notation "G1" => centralizer (Z1 : Set G)
local notation "MZ" => (G1 ⊓ Mc : Subgroup G)
local notation "Q1" => pCoreIn 2 MZ

/-- The concrete normalizer bound on O²(M_Z) used in source19. -/
theorem residual_normalizer_control
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hgen : M = (M ⊓ G1) ⊔ (T : Subgroup G))
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hTn : (T : Subgroup G) ≤ normalizer (MZ : Set G))
    (hSyl : ∃ P : Sylow 2 G1, (P : Subgroup G1).map (G1).subtype =
      (T : Subgroup G) ⊓ G1) :
    normalizer ((pResidual 2 MZ).map (MZ).subtype : Set G) ≤ Mc := by
  let J : Subgroup G := MZ ⊔ (T : Subgroup G)
  let Y : Subgroup G := (pResidual 2 MZ).map (MZ).subtype
  have huJ := (residual_and_uniqueness hZ hgen hM hu hne hres).2.2
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hJnorm : J ≤ normalizer (MZ : Set G) := sup_le (MZ).le_normalizer hTn
  have hQJ : Q1 ≤ J := (pCoreIn_le 2 _).trans le_sup_left
  have hJQ : J ≤ normalizer (Q1 : Set G) :=
    hJnorm.trans (normalizer_le_normalizer_characteristic_image MZ (pCore 2 MZ))
  have hQne := core_nontrivial hZ hZne hM hu h
  have hJHe : J ∈ Chapter1.He G := by
    apply Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T)
    refine ⟨?_,(show (T : Subgroup G) ≤ J from le_sup_right)⟩
    intro hb
    exact hQne (bot_unique ((le_pCoreIn_of_normalizes
      (isPGroup_pCoreIn 2 MZ) hQJ hJQ).trans_eq hb))
  have hYne : Y ≠ ⊥ := by
    intro hb
    have hr : pResidual 2 MZ = ⊥ :=
      ((pResidual 2 MZ).map_eq_bot_iff_of_injective (MZ).subtype_injective).mp hb
    have hp : IsPGroup 2 MZ := (isPGroup_quotient_pResidual 2).of_equiv
      ((QuotientGroup.quotientMulEquivOfEq hr).trans QuotientGroup.quotientBot)
    obtain ⟨P,hP⟩ := hSyl
    have hPMZ : (P : Subgroup G1) ≤ (MZ).subgroupOf G1 := by
      intro x hx
      have hm : (x : G) ∈ (T : Subgroup G) ⊓ G1 := hP ▸ mem_map_of_mem (G1).subtype hx
      exact ⟨hm.2,hTMc hm.1⟩
    have hEq := P.is_maximal' hp.comap_subtype hPMZ
    change (MZ).subgroupOf G1 = (P : Subgroup G1) at hEq
    have hmap := congrArg (fun A : Subgroup G1 => A.map (G1).subtype) hEq
    rw [map_subgroupOf_eq_of_le (show MZ ≤ G1 from inf_le_left),hP] at hmap
    have hJT : J = (T : Subgroup G) := sup_eq_right.mpr (hmap.le.trans inf_le_left)
    have hut : maximalTwoLocalOvergroups (T : Subgroup G) = {Mc} := hJT ▸ huJ
    simp only [hut,Set.ncard_singleton,lt_self_iff_false] at hmany
  have hJY : J ≤ normalizer (Y : Set G) :=
    hJnorm.trans (normalizer_le_normalizer_characteristic_image MZ (pResidual 2 MZ))
  exact normalizer_le_of_characteristic_two_unique
    (Chapter1.mem_He_iff.mp hJHe)
    (fun N hN hJN => Set.mem_singleton_iff.mp
      (huJ ▸ (show N ∈ maximalTwoLocalOvergroups J from ⟨hN,hJN⟩)))
    ((map_subtype_le _).trans le_sup_left) hYne hJY

end CaseIMarkedSubgroup
end CFSG.Quasithin.Chapter15.Section01
