module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SylowControl

/-!
# Residual and core-normalizer control for the Case-I marked subgroup

The actual source14(1) residual centralizes the marked subgroup Z₁, so it
lies in M_Z=C_G(Z₁)∩M_c. The Sylow supplement transfers uniqueness from
C_G(Z) to M_ZT. The Case-I generation identity forces C_M(Z₁) outside M_Z.
The nontrivial elementary Z₁ lies in O₂(M_Z). Once the source18(3)
normalization of M_Z by T is supplied, uniqueness controls every
characteristic-subgroup normalizer of this core and identifies its relative
normalizer with M_Z.

These proofs use the marked subgroup itself; they do not assume that the
later outside component has already been constructed.
Source: Aschbacher--Smith15.1.18(1),(2),(5),(7), printed pp.1092--1093.
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

/-- The residual containment, centralizer escape, and uniqueness from source18. -/
theorem residual_and_uniqueness (hZ : Z1 ≤ thompsonFixed T V)
    (hgen : M = (M ⊓ G1) ⊔ (T : Subgroup G))
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
        (centralizer (centralInvolutions T : Set G)).subtype ≤ MZ ∧
      ¬ M ⊓ G1 ≤ MZ ∧
      maximalTwoLocalOvergroups (MZ ⊔ (T : Subgroup G)) = {Mc} := by
  let C := centralizer (centralInvolutions T : Set G)
  have hMc : Mc ∈ maximalTwoLocalOvergroups C := hu ▸ Set.mem_singleton Mc
  have hTC : (T : Subgroup G) ≤ C := by
    intro t ht z hz
    exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm
  have hTMc : (T : Subgroup G) ≤ Mc := hTC.trans hMc.2
  have hresZ : (pResidual 2 C).map C.subtype ≤ MZ :=
    le_inf (hres.trans (centralizer_le hZ)) ((map_subtype_le _).trans hMc.2)
  have hesc : ¬ M ⊓ G1 ≤ MZ := by
    intro hc
    apply hne
    apply hM.1.1.eq_of_le hMc.1.1
    rw [hgen]
    exact sup_le (hc.trans inf_le_right) hTMc
  have hCJ : C ≤ MZ ⊔ (T : Subgroup G) := by
    have he := congrArg (map C.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTC))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTC] at he
    rw [←he]
    exact sup_le_sup_right hresZ _
  refine ⟨hresZ,hesc,?_⟩
  ext N
  constructor
  · rintro ⟨hN,hJN⟩
    exact Set.mem_singleton_iff.mpr (Set.mem_singleton_iff.mp
      (hu ▸ (show N ∈ maximalTwoLocalOvergroups C from ⟨hN,hCJ.trans hJN⟩)))
  · intro hN
    have he := Set.mem_singleton_iff.mp hN
    subst N
    exact ⟨hMc.1,sup_le inf_le_right hTMc⟩

/-- The marked elementary subgroup makes the literal two-core nontrivial. -/
theorem core_nontrivial (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) : Q1 ≠ ⊥ := by
  let := h.elementary
  have hZV : Z1 ≤ V := hZ.trans inf_le_left
  let : IsElementaryAbelian 2 Z1 := IsElementaryAbelian.of_injective
    (inclusion hZV) (inclusion_injective hZV)
  have hZT : Z1 ≤ (T : Subgroup G) := by
    intro z hz
    exact thompsonJ_le _ _ ((mem_omegaOneCenterAmbient_iff _ _).mp
      (h.thompsonFixed_le_omega T hM (hZ hz))).1
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hZMZ : Z1 ≤ MZ :=
    le_inf (le_centralizer_iff_isMulCommutative.mpr inferInstance) (hZT.trans hTMc)
  have hZQ : Z1 ≤ Q1 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 Z1) hZMZ
    (inf_le_left.trans (Subgroup.centralizer_le_normalizer _))
  exact fun he => hZne (bot_unique (hZQ.trans_eq he))

/-- Source18 core-normalizer control from the actual earlier normalization. -/
theorem core_normalizer_control (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hgen : M = (M ⊓ G1) ⊔ (T : Subgroup G))
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hTn : (T : Subgroup G) ≤ normalizer (MZ : Set G)) :
    (Q1).characteristicNormalizerClosure ≤ Mc ∧
      G1 ⊓ normalizer (Q1 : Set G) = MZ := by
  have huJ := (residual_and_uniqueness hZ hgen hM hu hne hres).2.2
  have hnQ : normalizer (MZ : Set G) ≤ normalizer (Q1 : Set G) :=
    normalizer_le_normalizer_characteristic_image MZ (pCore 2 MZ)
  have hMZQ : MZ ≤ normalizer (Q1 : Set G) := (MZ).le_normalizer.trans hnQ
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → MZ ⊔ (T : Subgroup G) ≤ N → N = Mc := by
    intro N hN hJN
    exact Set.mem_singleton_iff.mp (huJ ▸
      (show N ∈ maximalTwoLocalOvergroups (MZ ⊔ (T : Subgroup G)) from ⟨hN,hJN⟩))
  have hc : (Q1).characteristicNormalizerClosure ≤ Mc :=
    characteristicNormalizerClosure_le_of_unique_maximalTwoLocal huniq
      (isPGroup_pCoreIn 2 MZ) (sup_le hMZQ (hTn.trans hnQ))
  have hnMc : normalizer (Q1 : Set G) ≤ Mc :=
    (normalizer_le_characteristicNormalizerClosure_self Q1
      (core_nontrivial hZ hZne hM hu h)).trans hc
  exact ⟨hc,le_antisymm (inf_le_inf_left _ hnMc) (le_inf inf_le_left hMZQ)⟩

end CaseIMarkedSubgroup
end CFSG.Quasithin.Chapter15.Section01
