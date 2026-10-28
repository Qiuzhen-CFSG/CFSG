module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.FFModule
public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization.Thompson
public import Theory.GroupTheory.GeneralizedFitting.MovedComponent

/-!
# Thompson normalization of every original local-family member

The original central involutions normalize K because they centralize a full
Sylow subgroup. This is first proved on the actual two-core quotient and
then lifted through the solvable kernel. Since K has characteristic two,
the seed's commutators with K lie in O₂(K). Its image modulo O₂(KS) is
therefore a central two-subgroup and vanishes.

Consequently the seed's KS-span is reduced and elementary. It moves K by
the singleton centralizer-overgroup condition, so B.2.5 and B.1.5(4) give
J(S) ≤ N(K). K belongs only to L(G₁,S); neither ambient C-componenthood nor
S-normalization is assumed. No characteristic-two assertion about G₁ is used.

Source: Aschbacher--Smith 15.1.20(2), printed p.1094; B.1.5(4), B.2.5,
and B.2.14, printed pp.69,76,78.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
private theorem quasisimple_even (A : Type*) [Group A] [Finite A] [IsQuasisimple A] :
    2 ∣ Nat.card (A ⧸ center A) := by
  let : IsSimpleGroup (A ⧸ center A) := IsQuasisimple.simple
  by_contra hn
  have ho : Odd (Nat.card (A ⧸ center A)) := Nat.not_even_iff_odd.mp (fun he => hn (even_iff_two_dvd.mp he))
  exact Group.IsPerfect.not_isSolvable (A ⧸ center A) (_root_.odd_order_theorem _ ho)

private theorem central_seed_normalizes (P : Sylow 2 G) (K Z : Subgroup G)
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hZ : Z ≤ centralizer (P : Set G)) : Z ≤ normalizer (K : Set G) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let Q := K.map q
  have hc : IsComponent (G ⧸ pCore 2 G) Q :=
    ⟨hK.subnormal.quotient,IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)⟩
  let := hc.2
  have hz : Z.map q ≤ centralizer ((P.mapSurjective (f := q)
      (QuotientGroup.mk'_surjective _)) : Set (G ⧸ pCore 2 G)) := by
    rintro _ ⟨z,hz,rfl⟩ _ ⟨t,ht,rfl⟩
    exact (map_mul q t z).symm.trans ((congrArg q (hZ hz t ht)).trans (map_mul q z t))
  have hn := hc.centralizes_sylow_normalizes
    (P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)) (quasisimple_even Q) hz
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  rw [←normalizer_cComponent_quotient hK (pCore 2 G)]
  exact map_le_iff_le_comap.mp hn

private theorem central_seed_le_core (P : Sylow 2 G) (K Z : Subgroup G)
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hgen : K ⊔ (P : Subgroup G) = ⊤)
    (hf : generalizedFitting K = pCore 2 K)
    (hZP : Z ≤ P) (hZC : Z ≤ centralizer (P : Set G)) : Z ≤ pCore 2 G := by
  have hn := central_seed_normalizes P K Z hK hZC
  let R := K.pCoreIn 2
  have hRG : R ≤ pCore 2 G := pCoreIn_le_of_subnormal 2 hK.subnormal
  have hRP : R ≤ P := hRG.trans (pCore_isPGroup.le_sylow_of_normal P)
  have hZRC : Z ≤ centralizer (R : Set G) := hZC.trans (centralizer_le hRP)
  have hKN : K ≤ normalizer (centralizer (R : Set G) : Set G) :=
    (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))).trans
      (normalizer_le_normalizer_centralizer R)
  have hcommK : ⁅Z,K⁆ ≤ K := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp hn
  have hcommC : ⁅Z,K⁆ ≤ centralizer (R : Set G) :=
    (commutator_mono hZRC le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hKN)
  have hcomm : ⁅Z,K⁆ ≤ pCore 2 G := by
    intro x hx
    have hxK := hcommK hx
    have hc : (⟨x,hxK⟩ : K) ∈ centralizer (pCore 2 K : Set K) := by
      intro y hy
      exact Subtype.ext (hcommC hx y (mem_map_of_mem K.subtype hy))
    exact hRG (mem_map_of_mem K.subtype ((hf ▸ centralizer_generalizedFitting_le K) hc))
  let q := QuotientGroup.mk' (pCore 2 G)
  have hcK : Z.map q ≤ centralizer (K.map q : Set (G ⧸ pCore 2 G)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    exact hcomm
  have hcP : Z.map q ≤ centralizer ((P : Subgroup G).map q : Set (G ⧸ pCore 2 G)) := by
    rintro _ ⟨z,hz,rfl⟩ _ ⟨t,ht,rfl⟩
    exact (map_mul q t z).symm.trans ((congrArg q (hZC hz t ht)).trans (map_mul q z t))
  have hcent : Z.map q ≤ center (G ⧸ pCore 2 G) := by
    have ht : (⊤ : Subgroup (G ⧸ pCore 2 G)) ≤ centralizer (Z.map q : Set _) := by
      rw [←map_top_of_surjective q (QuotientGroup.mk'_surjective _),←hgen,Subgroup.map_sup]
      exact sup_le (le_centralizer_iff.mp hcK) (le_centralizer_iff.mp hcP)
    simpa only [coe_top,centralizer_univ] using le_centralizer_iff.mp ht
  let : (Z.map q).Normal := ⟨fun x hx g => by
    have hc := mem_center_iff.mp (hcent hx) g
    rwa [hc, mul_inv_cancel_right]⟩
  have hzcore : Z.map q ≤ pCore 2 (G ⧸ pCore 2 G) :=
    le_sSup ⟨inferInstance,(P.isPGroup'.to_le hZP).map q⟩
  have hzbot : Z.map q = ⊥ := bot_unique (hzcore.trans (pCore_quotient_pCore_eq_bot 2).le)
  simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff Z).mp hzbot

variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The original central-involution span is reduced for every constrained
local-family member, including those permuted by S. -/
theorem localFamily_catalogueModule_reduced_general (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : generalizedFitting K = pCore 2 K) : IsPReduced 2 (d.catalogueModule K) := by
  let H := K ⊔ d.S
  let K0 := K.subgroupOf H
  let Z := (centralInvolutions T).subgroupOf H
  obtain ⟨P,hP⟩ := hK.2.2.1
  have hZS : centralInvolutions T ≤ d.S := le_inf (centralInvolutions_le_sylow T)
    ((centralInvolutions_le_centralizer_sylow T).trans
      (centralizer_le (d.marked_le_sylow h hTM)))
  have hZT : Z ≤ P := by
    intro z hz
    obtain ⟨x,hx,he⟩ := hP.symm ▸ hZS hz
    exact H.subtype_injective he ▸ hx
  have hcent : Z ≤ centralizer (P : Set H) := by
    intro z hz x hx
    exact Subtype.ext (centralInvolutions_le_centralizer_sylow T hz x
      (d.S_le_T (hP ▸ mem_map_of_mem H.subtype hx)))
  let e : K0 ≃* K := subgroupOfEquivOfLe le_sup_left
  let := hq
  let : IsQuasisimple (K0 ⧸ pCore 2 K0) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hf0 : generalizedFitting K0 = pCore 2 K0 := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_generalizedFitting_equiv,pCore_map_iso,hf]
  have hgen : K0 ⊔ (P : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),hP,
      ←MonoidHom.range_eq_map,range_subtype]
  have hZQ := central_seed_le_core P K0 Z hK.2.1 hgen hf0 hZT hcent
  have hZC : Z ≤ centralizer (pCore 2 H : Set H) :=
    hcent.trans (centralizer_le (pCore_isPGroup.le_sylow_of_normal P))
  have hWQ : d.catalogueModule K ≤ pCore 2 H := normalClosure_le_normal hZQ
  have hWC : d.catalogueModule K ≤ centralizer (pCore 2 H : Set H) :=
    normalClosure_le_normal hZC
  let : IsMulCommutative (d.catalogueModule K) :=
    le_centralizer_iff_isMulCommutative.mp (hWC.trans (centralizer_le hWQ))
  let : IsElementaryAbelian 2 (centralInvolutions T) := by
    change IsElementaryAbelian 2 (omegaCenterIn (T : Subgroup G))
    infer_instance
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.subgroupOf (hZS.trans le_sup_right)
  let : IsMulCommutative (normalClosure (Z : Set H)) :=
    inferInstanceAs (IsMulCommutative (d.catalogueModule K))
  exact isPReduced_normalClosure_of_sylow_central P Z hZT hcent

/-- B.2.5 and B.1.5(4) normalize the actual local member. The seed comes
from the original T, even if the full Sylow subgroup S permutes K. -/
theorem localFamily_thompson_normalizes (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K) :
    elementaryAbelianMaxJ d.S ≤ normalizer (K : Set G) := by
  let H := K ⊔ d.S
  let W := d.catalogueModule K
  let K0 := K.subgroupOf H
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  have hr := d.localFamily_catalogueModule_reduced_general h hTM hK hq hf
  let := hr.elementary
  obtain ⟨P,hP⟩ := hK.2.2.1
  let e : K0 ≃* K := subgroupOfEquivOfLe le_sup_left
  let := hq
  have hq0 : IsQuasisimple (K0 ⧸ pCore 2 K0) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hne : K0.map q ≠ ⊥ := by
    intro hz
    have hc : K0 ≤ C := by simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff K0).mp hz
    exact d.localFamily_catalogueModule_moved h hTM hu hK hout
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))
  have hcore : pCore 2 H ≤ q.ker := by
    rw [QuotientGroup.ker_mk']
    exact le_centralizer_iff.mp hr.le_centralizer_pCore
  have hn := ChapterB.thompson_normalizes_surviving_cComponent W (P : Subgroup H) K0
    (hr.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal P)) hK.2.1 hq0
    q (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) hcore hne
  have hm := (map_mono (f := H.subtype) hn).trans (K0.le_normalizer_map H.subtype)
  rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP,
    map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left)] at hm
  exact hm


end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
