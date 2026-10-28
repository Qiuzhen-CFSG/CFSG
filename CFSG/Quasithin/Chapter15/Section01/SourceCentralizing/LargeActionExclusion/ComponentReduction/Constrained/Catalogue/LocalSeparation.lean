module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalFixed
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.OffenderSubgroup
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentSeparation
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates

/-!
# Original local-family support separation and nonblock exclusion

Use the original seed span in K join S as one common elementary module.
The image of K is an ordinary component in its faithful action quotient;
Thompson movement puts it in the normal offender-generated subgroup. The
actual SQTK cover supplies the complete B.5 classification there.

Normalization reflects through the two-core quotient, so a distinct
S-conjugate of K has a distinct surviving component image. The proved B.5
support separation therefore centralizes its moved space by K. Inclusion
of the original normalizer seed transports this to normalizerMoved K.
This discharges the separation premise of LocalFixed and proves original
rank-one nonblock placement in M_Z, without S-normality or ambient
C-componenthood. The original seed and central kernel are retained.

Source: Aschbacher--Smith C.1.16(3), pp.125--126, and 15.1.20(2),
pp.1094--1095. General Borel placement and catalogue exhaustiveness remain
with this catalogue owner; higher-field model residuals are separate inputs.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterB.SourceInduction
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

-- The common action, its genuine cover, and its surviving ordinary component.
theorem localFamily_orbit_action (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K) :
    let H := K ⊔ d.S
    let W := d.catalogueModule K
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
  let H := K ⊔ d.S
  let W := d.catalogueModule K
  have hr := d.localFamily_catalogueModule_reduced_general h hM.1.2 hK hq hf
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
    exact d.localFamily_catalogueModule_moved h hM.1.2 hu hK hout
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))
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
    exact (d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf).movement
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
    have hs := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
      ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
    have hHG : H ≤ d.G1 := sup_le hK.1 inf_le_right
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hHG)).mp (hs.subgroup (H.subgroupOf d.G1))
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
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterB.SourceInduction
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem map_conjugate {E D : Type*} [Group E] [Group D]
    (f : E →* D) (L : Subgroup E) (g : E) :
    (L.map (MulAut.conj g).toMonoidHom).map f =
      (L.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  ext x
  change f (g*x*g⁻¹) = f g * f x * (f g)⁻¹
  simp only [map_mul,map_inv]

/-- Embed the literal normalizer moved seed in the common K join S moved seed. -/
theorem normalizerMoved_le_catalogueMoved (d : CaseIComponentData T M Mc V) (K : Subgroup G) :
    d.normalizerMoved K ≤ (⁅d.catalogueModule K,K.subgroupOf (K ⊔ d.S)⁆).map
      (K ⊔ d.S).subtype := by
  let H0 := K ⊔ d.normalizerSylow K
  let H := K ⊔ d.S
  have hi : H0 ≤ H := sup_le le_sup_left (inf_le_left.trans le_sup_right)
  let i := inclusion hi
  have hU : (d.normalizerModule K).map i ≤ d.catalogueModule K := by
    apply map_le_iff_le_comap.mpr
    apply normalClosure_le_normal
    intro z hz
    exact le_normalClosure (show i z ∈ (centralInvolutions T).subgroupOf H from hz)
  have hK : (K.subgroupOf H0).map i = K.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_map,show H.subtype.comp i = H0.subtype from rfl,
      map_subgroupOf_eq_of_le (show K ≤ H0 from le_sup_left),
      map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left)]
  have hh : (⁅d.normalizerModule K,K.subgroupOf H0⁆).map i ≤
      ⁅d.catalogueModule K,K.subgroupOf H⁆ := by
    rw [map_commutator,hK]
    exact commutator_mono hU le_rfl
  have hm := map_mono (f := H.subtype) hh
  rw [map_map] at hm
  exact hm

/-- Distinct S-conjugates of the original moved support centralize K. -/
theorem localFamily_moved_separation (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    (g : G) (hg : g ∈ d.S) (hne : K.map (MulAut.conj g).toMonoidHom ≠ K) :
    (d.normalizerMoved K).map (MulAut.conj g).toMonoidHom ≤ centralizer (K : Set G) := by
  let H := K ⊔ d.S
  let W := d.catalogueModule K
  obtain ⟨hr,hA,hAJ,hclass,hreflect⟩ :=
    d.localFamily_orbit_action hG hempty hM hJ hu h hK hq hout hf
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
    (d.normalizerMoved_le_catalogueMoved K)
  rw [hm] at hbound
  intro w hw k hk
  obtain ⟨w0,hw0,rfl⟩ := hbound hw
  exact congrArg Subtype.val (hcentral hw0 ⟨k,mem_sup_left hk⟩ hk)

/-- Original rank-one nonblock placement, with every support and normalization premise discharged. -/
theorem localFamily_nonblock_le_MZ (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hf : generalizedFitting K = pCore 2 K)
    (hnot : ¬ ChapterC.IsChiBlock K)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) F) : K ≤ d.MZ := by
  by_contra hout
  exact hout (d.localFamily_nonblock_le_MZ_of_moved_separation hG hempty hM hJ hu h hK hq hf
    (d.localFamily_moved_separation hG hempty hM hJ hu h hK hq hout hf) hnot F e)

/-- An escaping local member with rank-one image in the literal normalizer
quotient is a chi-block. This is the source-image form of the nonblock argument;
the possibly central comparison kernel is retained. -/
theorem localFamily_rankOne_chi (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : d.normalizerImage K ≃* Matrix.SpecialLinearGroup (Fin 2) F) : ChapterC.IsChiBlock K := by
  obtain ⟨u,huW,hua,huc⟩ := d.localFamily_rankOne_fixed_witness
    hG hempty hM hJ hu h hK hq hout hf F e
  have hbaum : ChapterB.baumann d.S ≤ normalizer (K : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    by_contra hn
    have hfix : g*u*g⁻¹ = u := mul_inv_eq_iff_eq_mul.mpr (hg.2 u hua).symm
    have huim : u ∈ (d.normalizerMoved K).map (MulAut.conj g).toMonoidHom := by
      rw [←hfix]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom huW
    exact huc (d.localFamily_moved_separation hG hempty hM hJ hu h hK hq hout hf g hg.1 hn huim)
  exact d.localFamily_rankOne_chi_of_baumann_normalizes hG hempty hM hJ hu h hK hq hout hf hbaum F e

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
