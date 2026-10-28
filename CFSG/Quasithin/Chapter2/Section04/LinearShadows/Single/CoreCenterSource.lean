module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DistinguishedSource
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.Centers
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# Central involutions and the original local two-core

A nontrivial normal subgroup of T meets its center. The regular torus
propagates this central involution through the distinguished subgroup.
Characteristic two puts it in Z(O₂(M)), while uniqueness of M controls
its ambient centralizer.
Source: Aschbacher–Smith, proof of 2.4.18, printed p.534.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The regular torus carries a central Sylow involution through Z. Thus
Z lies in the center of O₂(M), and every nonidentity element of Z has its
ambient centralizer in the original unique maximal two-local subgroup. -/
theorem source_centerless_distinguished_core_center
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) = ⊥) :
    distinguishedZ d ≤ twoCore M ⊓ centralizer (twoCore M : Set G) ∧
      ∀ z ∈ distinguishedZ d, z ≠ 1 → centralizer ({z} : Set G) ≤ M := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Z := distinguishedZ d
  let P := twoCore M
  let C := P ⊓ centralizer (P : Set G)
  have hb := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  let : IsElementaryAbelian 2 Z := hb.1
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  have hZT : Z ≤ (T : Subgroup G) := hb.2.2.1.trans (inf_le_left.trans (hRS.trans hST.le))
  have hZn : Z ≠ ⊥ := by
    intro he
    have hcard : Nat.card Z = 2^n := hb.2.1
    rw [he,card_bot] at hcard
    have hp : 1 < 2^n := Nat.one_lt_pow (by have hn := hL.1; omega) (by decide)
    omega
  have hTZ := source_distinguished_normalized_by_sylow d hG T hST hsingle hL hz
  let ZT := Z.subgroupOf (T : Subgroup G)
  let : ZT.Normal := normal_subgroupOf_of_le_normalizer hTZ
  have hZTn : ZT ≠ ⊥ := by
    intro he
    have hm := congrArg (map (T : Subgroup G).subtype) he
    rw [map_subgroupOf_eq_of_le hZT,Subgroup.map_bot] at hm
    exact hZn hm
  obtain ⟨v,hv1⟩ := ne_bot_iff_exists_ne_one.mp
    (center_inf_ne_bot_of_normal T.isPGroup' ZT hZTn)
  let z : G := ((v : (T : Subgroup G)) : G)
  have hzZ : z ∈ Z := v.property.2
  have hzT : z ∈ T := (v : (T : Subgroup G)).property
  have hz1 : z ≠ 1 := fun he => hv1 (Subtype.ext (Subtype.ext he))
  have hzCT : z ∈ centralizer (T : Set G) := by
    intro t ht
    exact congrArg Subtype.val (mem_center_iff.mp v.property.1 (⟨t,ht⟩ : (T : Subgroup G)))
  have hPT : P ≤ (T : Subgroup G) := by
    change twoCore M ≤ (T : Subgroup G)
    simpa only [twoCore_eq_pCoreIn,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM]
      using pCoreIn_le_sylow M (T.subtype hTM)
  have hzCP : z ∈ centralizer (P : Set G) := centralizer_le hPT hzCT
  have hMe : M ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM)
  have hzC : z ∈ C := ⟨hMe ⟨hTM hzT,hzCP⟩,hzCP⟩
  have hzord : orderOf z = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z hzZ) hz1
  have hCz : centralizer ({z} : Set G) ≤ M := by
    apply centralizer_le_of_M_central_involution T hTM hunique hzord (T.subtype hTM)
    intro t ht
    have htT : t ∈ (T : Subgroup G) := by
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM] using ht
    exact mem_centralizer_iff.mp hzCT t htT
  obtain ⟨D,B,hDM,hDB,_,hcard,_,hodd,_,_,hBR,_,_,_,_,_,_,_,_,_,_,_,_⟩ :=
    source_fixed_free_torus d hG T hST hsingle hL hM hTM hunique
  have hr := source_centerless_torus_regular d hG T hST hsingle hL hM hTM hunique hz
    D (hDM.trans inf_le_right) (hodd.of_dvd_nat (card_dvd_of_le hDB)) hcard (hDB.trans hBR)
  have hreg : ∀ w ∈ Z, w ≠ 1 → ∃ a : D, (a:G)*z*(a:G)⁻¹=w := by
    intro w hw hw1
    have hZeq := distinguishedZ_of_centerless d hz
    obtain ⟨a,ha,_⟩ := hr.2 z (hZeq ▸ hzZ) hz1 w (hZeq ▸ hw) hw1
    exact ⟨a,ha⟩
  have hMC : M ≤ normalizer (C : Set G) :=
    (le_inf (le_normalizer_twoCore M)
      ((le_normalizer_twoCore M).trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf
  refine ⟨?_,?_⟩
  · intro w hw
    by_cases hw1 : w=1
    · exact hw1 ▸ C.one_mem
    obtain ⟨a,ha⟩ := hreg w hw hw1
    exact ha ▸ (mem_normalizer_iff.mp (hMC ((hDM.trans inf_le_left) a.property)) z).mp hzC
  · intro w hw hw1
    obtain ⟨a,ha⟩ := hreg w hw hw1
    let e := MulAut.conj (a:G)
    have he : (centralizer ({z} : Set G)).map e.toMonoidHom = centralizer ({w} : Set G) := by
      rw [Theory.GroupTheory.map_centralizer_equiv,Set.image_singleton]
      exact congrArg (fun y : G => centralizer ({y} : Set G)) ha
    rw [← he]
    exact (map_mono hCz).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (M.le_normalizer ((hDM.trans inf_le_left) a.property)))
end CFSG.Quasithin.Chapter2.LinearShadows.Single
