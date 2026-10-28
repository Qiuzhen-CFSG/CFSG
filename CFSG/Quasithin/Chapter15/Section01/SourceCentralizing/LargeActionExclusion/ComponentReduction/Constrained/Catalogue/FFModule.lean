module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalFamily
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.CentralSeed
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import Theory.GroupTheory.ElementaryThompsonQuasisimpleCore
public import Theory.GroupTheory.GeneralizedFitting.InternalModuleResidual.Quasisimple
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
public import Theory.GroupTheory.SelfCentralizingCorePGroupJoin

/-!
# The original FF-module in the normalized local-family branch

For a member K of the fixed family L(G₁,S) normalized by S, characteristic
two passes from K to KS. The normal closure of the original Ω₁Z(T) lies
in Ω₁Z(O₂(KS)); its Sylow-central seed makes it reduced. The singleton
centralizer overgroup forces K to move that seed. The literal centralizer
quotient then has quasisimple generalized Fitting subgroup equal to the
image of K and satisfies O₂(KS)=C_S(U).

The earlier Thompson-normalizer obstruction gives both K=[K,J(S)] and an
actual FF-module on this quotient. K need not be an ambient C-component,
and no later exchanged marker, unidentified quotient model, or Q₁ action
is assumed. S-normalization remains an explicit branch condition; this
module does not assert the full source catalogue.

Source: Aschbacher--Smith 15.1.20(2), printed p.1094, using B.2.7, B.2.14
and the quasisimple internal-module argument of B.2.10, pp.76--78.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
namespace CaseIComponentData
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

@[expose] def catalogueModule (d : CaseIComponentData T M Mc V) (K : Subgroup G) :
    Subgroup (K ⊔ d.S : Subgroup G) :=
  normalClosure ((centralInvolutions T).subgroupOf (K ⊔ d.S) : Set (K ⊔ d.S : Subgroup G))

instance catalogueModule_normal (d : CaseIComponentData T M Mc V) (K : Subgroup G) :
    (d.catalogueModule K).Normal := by unfold catalogueModule; infer_instance

private theorem catalogue_seed_le_S (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M) :
    centralInvolutions T ≤ d.S :=
  le_inf (centralInvolutions_le_sylow T)
    ((centralInvolutions_le_centralizer_sylow T).trans
      (centralizer_le (d.marked_le_sylow h hTM)))

/-- The original central-involution span is reduced in the normalized local branch. -/
theorem localFamily_catalogueModule_reduced (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hf : generalizedFitting K = pCore 2 K)
    (hn : d.S ≤ normalizer (K : Set G)) : IsPReduced 2 (d.catalogueModule K) := by
  let H := K ⊔ d.S
  let Z := (centralInvolutions T).subgroupOf H
  obtain ⟨P,hP⟩ := hK.2.2.1
  have hZS := d.catalogue_seed_le_S h hTM
  have hZT : Z ≤ P := by
    intro z hz
    obtain ⟨x,hx,he⟩ := hP.symm ▸ hZS hz
    exact H.subtype_injective he ▸ hx
  have hcent : Z ≤ centralizer (P : Set H) := by
    intro z hz x hx
    exact Subtype.ext (centralInvolutions_le_centralizer_sylow T hz x
      (d.S_le_T (hP ▸ mem_map_of_mem H.subtype hx)))
  have hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    centralizer_pCore_sup_le 2 K d.S
      (hf ▸ centralizer_generalizedFitting_le K)
      (T.isPGroup'.to_le d.S_le_T) hn
  have hZC : Z ≤ centralizer (pCore 2 H : Set H) :=
    hcent.trans (centralizer_le (pCore_isPGroup.le_sylow_of_normal P))
  have hWQ : d.catalogueModule K ≤ pCore 2 H := normalClosure_le_normal (hZC.trans hchar)
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

/-- The same literal seed forces nontrivial action, without choosing a model. -/
theorem localFamily_catalogueModule_moved (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S) (hout : ¬ K ≤ d.MZ) :
    ⁅d.catalogueModule K,K.subgroupOf (K ⊔ d.S)⁆ ≠ ⊥ := by
  intro he
  have hc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
  have hZH := (d.catalogue_seed_le_S h hTM).trans (show d.S ≤ K ⊔ d.S from le_sup_right)
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  apply hout
  apply le_inf hK.1
  intro k hk
  apply hMc.2
  intro z hz
  exact congrArg Subtype.val (hc (show (⟨k,mem_sup_left hk⟩ : (K ⊔ d.S : Subgroup G)) ∈
    K.subgroupOf (K ⊔ d.S) from hk) ⟨z,hZH hz⟩ (le_normalClosure hz))

/-- In the normalized local branch, source Thompson escape gives full movement. -/
theorem localFamily_eq_commutator_of_normalizes (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hn : d.S ≤ normalizer (K : Set G)) : K = ⁅K,elementaryAbelianMaxJ d.S⁆ := by
  let H := K ⊔ d.S
  let K0 := K.subgroupOf H
  let : K0.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer hn)
  let e : K0 ≃* K := subgroupOfEquivOfLe le_sup_left
  let := hq
  let : IsQuasisimple (K0 ⧸ pCore 2 K0) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  obtain ⟨P,hP⟩ := hK.2.2.1
  have hgen : K0 ⊔ (P : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),hP,
      ←MonoidHom.range_eq_map,range_subtype]
  have hnot : ¬ K0 ≤ normalizer (elementaryAbelianMaxJ (P : Subgroup H) : Set H) := by
    intro hh
    have hm := (map_mono (f := H.subtype) hh).trans
      ((elementaryAbelianMaxJ (P : Subgroup H)).le_normalizer_map H.subtype)
    rw [map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP] at hm
    exact d.localFamily_thompson_escape hG hempty hM hJ hu h hK hout hm
  have he := congrArg (map H.subtype)
    (eq_commutator_maxJ_of_quasisimple_core_of_not_normalizes P K0 hK.2.1 hgen hnot)
  rwa [map_commutator,map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
    ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP] at he

/-- The actual local action data used before the B.4.2 classification.
The module is fixed by definition; none of the catalogue alternatives is a field. -/
structure CatalogueAction (d : CaseIComponentData T M Mc V) (K : Subgroup G) : Prop where
  reduced : IsPReduced 2 (d.catalogueModule K)
  movement : K = ⁅K,elementaryAbelianMaxJ d.S⁆
  core : pCore 2 (K ⊔ d.S : Subgroup G) =
    d.S.subgroupOf (K ⊔ d.S) ⊓ centralizer (d.catalogueModule K : Set (K ⊔ d.S : Subgroup G))
  fitting :
    let q := QuotientGroup.mk' (centralizer (d.catalogueModule K : Set (K ⊔ d.S : Subgroup G)))
    (K.subgroupOf (K ⊔ d.S)).map q = generalizedFitting _
  quasisimple :
    let q := QuotientGroup.mk' (centralizer (d.catalogueModule K : Set (K ⊔ d.S : Subgroup G)))
    IsQuasisimple ((K.subgroupOf (K ⊔ d.S)).map q)
  ff :
    letI := reduced.elementary
    let q := QuotientGroup.mk' (centralizer (d.catalogueModule K : Set (K ⊔ d.S : Subgroup G)))
    IsFFModule (NormalElementaryQuotient.representation (d.catalogueModule K) q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _))

/-- The FF-module opening of 15.1.20(2) for an S-normalized local-family member,
with its original central-involution seed and literal centralizer quotient. -/
theorem localFamily_catalogueAction_of_normalizes (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    (hn : d.S ≤ normalizer (K : Set G)) : d.CatalogueAction K := by
  let H := K ⊔ d.S
  let K0 := K.subgroupOf H
  let W := d.catalogueModule K
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  have hr := d.localFamily_catalogueModule_reduced h hM.1.2 hK hf hn
  let := hr.elementary
  let : K0.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer hn)
  let e : K0 ≃* K := subgroupOfEquivOfLe le_sup_left
  let := hq
  let : IsQuasisimple (K0 ⧸ pCore 2 K0) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  obtain ⟨P,hP⟩ := hK.2.2.1
  have hPS : (P : Subgroup H) = d.S.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (show d.S ≤ H from le_sup_right)]
  have hgen : K0 ⊔ (P : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),hP,
      ←MonoidHom.range_eq_map,range_subtype]
  have hprod : ∀ x : H, ∃ k ∈ K0, ∃ t ∈ (P : Subgroup H), k*t=x := by
    intro x
    exact mem_sup_of_normal_left.mp (hgen.symm ▸ mem_top x)
  obtain ⟨hcore,_,hfit,hquasi⟩ := internalModule_quasisimple_core_structure
    W q (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    hr.quotient_pCore_eq_bot P K0 hK.2.1 inferInstance
    (d.localFamily_catalogueModule_moved h hM.1.2 hu hK hout) hprod
  refine ⟨hr,d.localFamily_eq_commutator_of_normalizes hG hempty hM hJ hu h hK hq hout hn,
    hPS ▸ hcore,hfit,hquasi,?_⟩
  have hnot : ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ q.ker := by
    intro hh
    have hJP : elementaryAbelianMaxJ (P : Subgroup H) ≤ P := sSup_le fun _ hA => hA.1
    have hhC : elementaryAbelianMaxJ (P : Subgroup H) ≤ C := by
      simpa only [q,QuotientGroup.ker_mk'] using hh
    have hJQ : elementaryAbelianMaxJ (P : Subgroup H) ≤ pCore 2 H :=
      hcore.symm ▸ le_inf hJP hhC
    have hm := map_mono (f := H.subtype) hJQ
    rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP] at hm
    exact d.localFamily_thompson_not_le_core hG hempty hM hJ hu h hK hout hm
  exact (ChapterB.lemma_B_2_7_local W q (QuotientGroup.mk'_surjective C)
    (QuotientGroup.ker_mk' C) P (hr.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal P)) hnot).1

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
