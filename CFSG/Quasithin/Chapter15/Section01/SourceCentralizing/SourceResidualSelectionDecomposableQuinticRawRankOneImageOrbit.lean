module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawNormalizer
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalSeparation
-- Reuse the intrinsic central-seed proof, without constructing component data.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.Normalizer

/-! Distinct S-conjugates of the actual normalizer moved seed centralize
its component. The proof uses the original common seed span and the proved
B.5 separation of surviving ordinary components in its faithful action. -/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterB.SourceInduction
variable {G : Type*} [Group G] [Finite G]

private theorem raw_common_seed_reduced
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 K : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (_hZne : Z1 ≠ ⊥)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hf : generalizedFitting K = pCore 2 K)
    (hout : ¬K ≤ centralizer (Z1 : Set G) ⊓ Mc) (houtM : ¬K ≤ M) :
    IsPReduced 2 (normalClosure ((centralInvolutions T).subgroupOf (K ⊔ ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))) : Set (K ⊔ ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) : Subgroup G))) := by
  let S := ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
  let H := K ⊔ S
  let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
  let K0 := K.subgroupOf H
  let Z := (centralInvolutions T).subgroupOf H
  obtain ⟨P,hP⟩ := hK.2.2.1
  have hZS : centralInvolutions T ≤ S :=
    (h.raw_component_thompson hG T hM hJ hu hZ hK hq hf hout houtM).2.2.2.2.trans inf_le_left
  have hZT : Z ≤ P := by
    intro z hz
    have hzP : (z : G) ∈ (P : Subgroup H).map H.subtype := by
      rw [hP]
      exact hZS hz
    obtain ⟨x,hx,he⟩ := hzP
    exact H.subtype_injective he ▸ hx
  have hcent : Z ≤ centralizer (P : Set H) := by
    intro z hz x hx
    exact Subtype.ext (centralInvolutions_le_centralizer_sylow T hz x
      ((show (x : G) ∈ (T : Subgroup G) from (hP ▸ mem_map_of_mem H.subtype hx).1)))
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
  have hZQ := CaseIComponentData.central_seed_le_core P K0 Z hK.2.1 hgen hf0 hZT hcent
  have hZC : Z ≤ centralizer (pCore 2 H : Set H) :=
    hcent.trans (centralizer_le (pCore_isPGroup.le_sylow_of_normal P))
  have hWQ : W ≤ pCore 2 H := normalClosure_le_normal hZQ
  have hWC : W ≤ centralizer (pCore 2 H : Set H) :=
    normalClosure_le_normal hZC
  let : IsMulCommutative W :=
    le_centralizer_iff_isMulCommutative.mp (hWC.trans (centralizer_le hWQ))
  let : IsElementaryAbelian 2 (centralInvolutions T) := by
    change IsElementaryAbelian 2 (omegaCenterIn (T : Subgroup G))
    infer_instance
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.subgroupOf (hZS.trans le_sup_right)
  let : IsMulCommutative (normalClosure (Z : Set H)) :=
    inferInstanceAs (IsMulCommutative W)
  exact isPReduced_normalClosure_of_sylow_central P Z hZT hcent

private theorem raw_common_orbit_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 K : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hf : generalizedFitting K = pCore 2 K)
    (hout : ¬K ≤ centralizer (Z1 : Set G) ⊓ Mc) (houtM : ¬K ≤ M) :
    let S := ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
    let H := K ⊔ S
    let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    ∃ hr : IsPReduced 2 W,
      letI := hr.elementary
      let C := centralizer (W : Set H)
      let q := QuotientGroup.mk' C
      let ρ := NormalElementaryQuotient.representation W q
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
      let A := (K.subgroupOf H).map q
      let J := offenderSubgroup ρ
      IsComponent (H ⧸ C) A ∧ A ≤ J ∧
        AdequateAlternative (ρ.comp J.subtype) ∧
        ∀ x : H, q x ∈ normalizer (A : Set (H ⧸ C)) →
          (x : G) ∈ normalizer (K : Set G) := by
  let S := ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
  let H := K ⊔ S
  let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
  have hr := raw_common_seed_reduced hG T hM hJ hu h hZ hZne hK hq hf hout houtM
  let := hr.elementary
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let A := (K.subgroupOf H).map q
  let J := offenderSubgroup ρ
  let K0 := K.subgroupOf H
  let e : K0 ≃* K := subgroupOfEquivOfLe le_sup_left
  let := hq
  have hq0 : IsQuasisimple (K0 ⧸ pCore 2 K0) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hcore : pCore 2 H ≤ q.ker := by
    rw [QuotientGroup.ker_mk']
    exact le_centralizer_iff.mp hr.le_centralizer_pCore
  have hne : A ≠ ⊥ := by
    intro he
    have hc : K0 ≤ C := by simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff K0).mp he
    have hZR := (h.raw_component_thompson hG T hM hJ hu hZ hK hq hf hout houtM).2.2.2.2
    have hMc : Mc ∈ maximalTwoLocalOvergroups
        (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
    apply hout
    refine le_inf hK.1 ?_
    intro k hk
    apply hMc.2
    intro z hz
    exact congrArg Subtype.val (hc (show (⟨k,mem_sup_left hk⟩ : H) ∈ K0 from hk)
      ⟨z,mem_sup_right ((show centralInvolutions T ≤ S from hZR.trans inf_le_left) hz)⟩
      (le_normalClosure hz))
  have hA : IsComponent (H ⧸ C) A := hK.2.1.isComponent_map_of_twoCore_killed hq0 q
    (QuotientGroup.mk'_surjective C) ((pCoreIn_le_of_subnormal 2 hK.2.1.subnormal).trans hcore) hne
  obtain ⟨P,hP⟩ := hK.2.2.1
  have hJP : (elementaryAbelianMaxJ (P : Subgroup H)).map q ≤ J := by
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro B hB b hb
    by_cases hB0 : B.map q = ⊥
    · change q b ∈ J
      rw [show q b = 1 from (map_eq_bot_iff B).mp hB0 hb]
      exact one_mem J
    · exact (NormalElementaryQuotient.maxElementary_isBestOffender W q
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) (P : Subgroup H) B
        (hr.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal P)) hB hB0).le_offenderSubgroup ρ
        (mem_map_of_mem q hb)
  have hmove : K0 = ⁅K0,elementaryAbelianMaxJ (P : Subgroup H)⁆ := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP]
    exact (h.raw_component_thompson hG T hM hJ hu hZ hK hq hf hout houtM).2.1.symm
  have hAJ : A ≤ J := by
    let : J.Normal := offenderSubgroup_normal ρ
    have hm : A = ⁅A,(elementaryAbelianMaxJ (P : Subgroup H)).map q⁆ := by
      change K0.map q = _
      conv_lhs => rw [hmove]
      rw [map_commutator]
    rw [hm]
    exact (commutator_mono le_rfl hJP).trans (commutator_le_right A J)
  have hsq : IsSQTK KnownSimple.IsKnownSimple H := by
    let := h.elementary
    have hs := caseI_centralizer_sqtk hG Z1 hZne
      ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left))
    have hHG : H ≤ (centralizer (Z1 : Set G)) := sup_le hK.1 inf_le_right
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hHG)).mp (hs.subgroup (H.subgroupOf (centralizer (Z1 : Set G))))
  let cover : SQTKQuotient KnownSimple.IsKnownSimple (H ⧸ C) :=
    ⟨H,C,hsq,MulEquiv.refl _⟩
  have hc := offenderSubgroup_adequateAlternative ρ
    (NormalElementaryQuotient.representation_injective W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C))
    hr.quotient_pCore_eq_bot cover
  refine ⟨hr,hA,hAJ,hc,?_⟩
  intro x hx
  let q0 := QuotientGroup.mk' (pCore 2 H)
  let f := QuotientGroup.lift (pCore 2 H) q hcore
  have hcomp : f.comp q0 = q := by ext; rfl
  have hA0 : IsComponent (H ⧸ pCore 2 H) (K0.map q0) :=
    hK.2.1.isComponent_map_of_twoCore_killed hq0 q0 (QuotientGroup.mk'_surjective _)
      (by simpa only [q0,QuotientGroup.ker_mk'] using pCoreIn_le_of_subnormal 2 hK.2.1.subnormal)
      (by
        intro he
        apply hne
        change K0.map q = ⊥
        rw [←hcomp,←map_map,he,Subgroup.map_bot])
  have hn0 : q0 x ∈ normalizer (K0.map q0 : Set (H ⧸ pCore 2 H)) :=
    hA0.mem_normalizer_of_mem_normalizer_map f
      (by rwa [map_map,hcomp]) (by
        rw [map_map,hcomp]
        change q x ∈ normalizer (K0.map q : Set (H ⧸ C))
        exact hx)
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  have hn : x ∈ normalizer (K0 : Set H) := by
    rwa [←normalizer_cComponent_quotient hK.2.1 (pCore 2 H)]
  have hh := K0.le_normalizer_map H.subtype (mem_map_of_mem H.subtype hn)
  rwa [map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left)] at hh

private theorem map_conjugate {E D : Type*} [Group E] [Group D]
    (f : E →* D) (L : Subgroup E) (g : E) :
    (L.map (MulAut.conj g).toMonoidHom).map f =
      (L.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  ext x
  change f (g*x*g⁻¹) = f g * f x * (f g)⁻¹
  simp only [map_mul,map_inv]

omit [Finite G] in
private theorem raw_normalizerMoved_le_common (T : Sylow 2 G) (Z1 K : Subgroup G) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let H0 := K ⊔ (S ⊓ normalizer (K : Set G))
    let H := K ⊔ S
    let U := normalClosure ((centralInvolutions T).subgroupOf H0 : Set H0)
    let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    (⁅U,K.subgroupOf H0⁆).map H0.subtype ≤ (⁅W,K.subgroupOf H⁆).map H.subtype := by
  let H0 := K ⊔ (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ normalizer (K : Set G))
  let H := K ⊔ ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
  have hi : H0 ≤ H := sup_le le_sup_left (inf_le_left.trans le_sup_right)
  let i := inclusion hi
  have hU : (normalClosure ((centralInvolutions T).subgroupOf H0 : Set H0)).map i ≤ normalClosure ((centralInvolutions T).subgroupOf H : Set H) := by
    apply map_le_iff_le_comap.mpr
    apply normalClosure_le_normal
    intro z hz
    exact le_normalClosure (show i z ∈ (centralInvolutions T).subgroupOf H from hz)
  have hK : (K.subgroupOf H0).map i = K.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_map,show H.subtype.comp i = H0.subtype from rfl,
      map_subgroupOf_eq_of_le (show K ≤ H0 from le_sup_left),
      map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left)]
  have hh : (⁅normalClosure ((centralInvolutions T).subgroupOf H0 : Set H0),K.subgroupOf H0⁆).map i ≤
      ⁅normalClosure ((centralInvolutions T).subgroupOf H : Set H),K.subgroupOf H⁆ := by
    rw [map_commutator,hK]
    exact commutator_mono hU le_rfl
  have hm := map_mono (f := H.subtype) hh
  rw [map_map] at hm
  exact hm

theorem PreparedChosenModule.raw_component_moved_separation
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 K : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hf : generalizedFitting K = pCore 2 K)
    (hout : ¬K ≤ centralizer (Z1 : Set G) ⊓ Mc) (houtM : ¬K ≤ M)
    (g : G) (hg : g ∈ ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hne : K.map (MulAut.conj g).toMonoidHom ≠ K) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let H := K ⊔ (S ⊓ normalizer (K : Set G))
    let U := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    ((⁅U,K.subgroupOf H⁆).map H.subtype).map (MulAut.conj g).toMonoidHom ≤
      centralizer (K : Set G) := by
  dsimp only
  let S := ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
  let H := K ⊔ S
  let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
  obtain ⟨hr,hA,hAJ,hclass,hreflect⟩ :=
    raw_common_orbit_action hG T hM hJ hu h hZ hZne hK hq hf hout houtM
  let := hr.elementary
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let A := (K.subgroupOf H).map q
  let J := offenderSubgroup ρ
  let : J.Normal := offenderSubgroup_normal ρ
  let x : H := ⟨g,mem_sup_right hg⟩
  let B := A.map (MulAut.conj (q x)).toMonoidHom
  have hB : IsComponent (H ⧸ C) B := hA.map_conj (q x)
  have hBJ : B ≤ J := by
    rintro _ ⟨a,ha,rfl⟩
    exact (inferInstance : J.Normal).conj_mem a (hAJ ha) (q x)
  have hBA : B ≠ A := by
    intro he
    exact hne (mem_normalizer_iff_map_conj_eq.mp
      (hreflect x (mem_normalizer_iff_map_conj_eq.mpr he)))
  have hBA' : B.subgroupOf J ≠ A.subgroupOf J := by
    intro he
    have hm := congrArg (map J.subtype) he
    rw [map_subgroupOf_eq_of_le hBJ,map_subgroupOf_eq_of_le hAJ] at hm
    exact hBA hm
  have hcross := hclass.distinct_components_cross (hB.subgroupOf hBJ) (hA.subgroupOf hAJ) hBA'
  have hcross0 : subspaceCommutator ρ ⊤ B ≤ fixedSpace ρ A := by
    intro v hv a
    have hv' : v ∈ subspaceCommutator (ρ.comp J.subtype) ⊤ (B.subgroupOf J) := by
      simpa only [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hBJ] using hv
    exact hcross hv' ⟨⟨a,hAJ a.property⟩,a.property⟩
  let Kx := (K.subgroupOf H).map (MulAut.conj x).toMonoidHom
  have hKx : Kx.map q = B := map_conjugate q (K.subgroupOf H) x
  have hcentral : ⁅W,Kx⁆ ≤ centralizer (K.subgroupOf H : Set H) := by
    intro w hw k hk
    let v : Additive W := Additive.ofMul ⟨w,(commutator_le_left W Kx) hw⟩
    have hv : v ∈ subspaceCommutator ρ ⊤ B := by
      rw [←hKx,←NormalElementaryQuotient.commutatorSpace_eq W q
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) Kx]
      exact hw
    have hh := hcross0 hv ⟨q k,mem_map_of_mem q hk⟩
    have he := congrArg (fun a : Additive W => (a.toMul : H)) hh
    change ((NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) (q k) v).toMul : H) = w at he
    rw [NormalElementaryQuotient.representation_apply] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hnW : W.map (MulAut.conj x).toMonoidHom = W :=
    mem_normalizer_iff_map_conj_eq.mp (show x ∈ normalizer (W : Set H) by
      rw [normalizer_eq_top]; trivial)
  have hm : ((⁅W,K.subgroupOf H⁆).map H.subtype).map (MulAut.conj g).toMonoidHom =
      (⁅W,Kx⁆).map H.subtype := by
    change ((⁅W,K.subgroupOf H⁆).map H.subtype).map
      (MulAut.conj (H.subtype x)).toMonoidHom = _
    rw [←map_conjugate H.subtype (⁅W,K.subgroupOf H⁆) x,map_commutator,hnW]
  have hbound := map_mono (f := (MulAut.conj g).toMonoidHom)
    (raw_normalizerMoved_le_common T Z1 K)
  rw [hm] at hbound
  intro w hw k hk
  obtain ⟨w0,hw0,rfl⟩ := hbound hw
  exact congrArg Subtype.val (hcentral hw0 ⟨k,mem_sup_left hk⟩ hk)

end CFSG.Quasithin.Chapter15.Section01
