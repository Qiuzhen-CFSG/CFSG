module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalComponentGeometry
public import Theory.SpecificGroups.G2Even.BinarySylowOvergroups
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalComponentGeometry

import all CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction

import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.G2Parabolics
import all Theory.SpecificGroups.G2Even.CoreParabolics

/-!
# The full original G₂ marked-parabolic geometry

A nonidentity automorphism fixing a block Sylow modulo its center is inner
by a natural fixed vector. A concrete cubic also fixes that vector, so its
stabilizer is a strict Sylow overgroup in G₂(2)′ and is maximal. The original
seed realizes the entire order-two fixer group. Central-kernel Sylow detection
then identifies the marked intersection with both literal centralizers,
including the full central attachment of U(K), for every eligible local K.

The two native parabolics lift through the original two-core with one common
conjugator. Their maximality and source-family placement identify them with
M_Z ∩ L and M ∩ L in opposite positions. The original FF marking is unchanged;
the conjugator is recorded explicitly in the two quotient images. Original
marker and exchanged applications retain these maps and both centralizers.

The import-all edges continue the preceding internal block and parabolic
arguments without changing their public boundaries. The natural fixed-vector
and native parabolic calculations inherit the licensed ATLAS attribution.
Source: Aschbacher--Smith 15.1.20(2b) and 15.1.22(2), printed pp.1094--1100.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC Atlas.G2.Natural Atlas.G2.BinaryParabolicPair
open Section03 Section03.InitialSource ChapterA.Section05To06

private theorem g2_action_injective : Function.Injective g2TwoNaturalAction := by
  intro g h hh
  apply Subtype.ext
  apply action_injective (ZMod 2)
  apply LinearMap.ext
  intro v
  exact congrArg Multiplicative.toAdd (DFunLike.congr_fun hh (Multiplicative.ofAdd v))

private theorem g2_sylow_overgroup (Q : Sylow 2 DerivedModel)
    (C : Subgroup DerivedModel) (hC : C ≠ ⊤) (hQ : (Q : Subgroup DerivedModel) < C) :
    IsCoatom C := by
  obtain ⟨_,f,_,hf⟩ := SolvableSylowControl.exists_aligned_equiv
    (MulEquiv.refl DerivedModel) Q derivedSylow
  apply (f.mapSubgroup.isCoatom_iff C).mp
  apply Atlas.G2.BinarySylowOvergroups.overgroup_isCoatom
  · intro he
    apply hC
    apply map_injective (f := f.toMonoidHom) f.injective
    exact he.trans (map_top_of_surjective f.toMonoidHom f.surjective).symm
  · rw [←hf]
    exact (f.mapSubgroup.lt_iff_lt).mpr hQ

private theorem g2_fixer_parabolic
    {A : Type*} [Group A] [Finite A] (hb : IsG2TwoBlock A)
    (P : Sylow 2 A) (a : MulAut A) (ha : a ≠ 1)
    (hP : ∀ x ∈ P, a x * x⁻¹ ∈ center A) :
    ∃ J : Subgroup A, IsCoatom J ∧ ∀ x ∈ J, a x * x⁻¹ ∈ center A := by
  obtain ⟨m⟩ := hb.natural_model
  have hk : IsPGroup 2 m.actor.ker := by
    rw [BlockModuleModel.actor,MonoidHom.ker_comp_of_injective _ _ m.quotientIso.injective,
      QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let : Group.IsPerfect DerivedModel := by
    rw [DerivedModel,commutator_eq_longRootClosure]
    exact Atlas.G2.BinaryException.H_isPerfect
  let : Group.IsPerfect A := hb.short.twoPerfect.isPerfect_of_surjective_pGroup_kernel
    m.actor m.actor_surjective hk
  obtain ⟨u,hu,hfix⟩ := hb.short.automorphism_eq_conj_of_central_sylow
    m g2_action_injective P a hP
  let w := m.moduleIso (QuotientGroup.mk' (blockFixed A) u)
  let Q := P.mapSurjective m.actor_surjective
  let C := (MulAction.stabilizer (MulAut (Multiplicative (Space (ZMod 2)))) w).comap
    g2TwoNaturalAction
  have hJC (x : A) (hx : x ∈ C.comap m.actor) : a x * x⁻¹ ∈ center A := by
    have hh : QuotientGroup.mk' (blockFixed A) (blockConjugate A x u) =
        QuotientGroup.mk' (blockFixed A) u :=
      m.moduleIso.injective ((m.intertwining x u).trans hx)
    have hz : x * (u : A) * x⁻¹ * (u : A)⁻¹ ∈ center A := by
      have hh' := QuotientGroup.eq_iff_div_mem.mp hh
      simp only [div_eq_mul_inv] at hh'
      exact hh'
    have hz' := (center A).inv_mem hz
    rw [hu]
    simpa only [MulAut.conj_apply,mul_inv_rev,inv_inv,mul_assoc] using hz'
  have hC : C ≠ ⊤ := by
    intro he
    apply ha
    apply MulAut.quotient_center_injective
    ext z
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center A) z
    rw [quotientAut_apply_mk,quotientAut_apply_mk]
    change QuotientGroup.mk' (center A) (a x) = QuotientGroup.mk' (center A) x
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa only [div_eq_mul_inv] using hJC x (show m.actor x ∈ C from he ▸ mem_top _)
  have hQC : (Q : Subgroup DerivedModel) ≤ C := by
    rintro _ ⟨x,hx,rfl⟩
    exact hfix x hx
  obtain ⟨c,hc,_,hcf⟩ := BinarySylowFixedSpace.derived_sylow_enlargement Q
  have hw : w.toAdd ∈ fixedSpace (g2DerivedNatural (ZMod 2)) (Q : Subgroup DerivedModel) := by
    rintro ⟨g,hg⟩
    exact congrArg Multiplicative.toAdd (hQC hg)
  have hcC : c ∈ C := by
    apply Multiplicative.toAdd.injective
    exact hcf w.toAdd hw
  have hQlt : (Q : Subgroup DerivedModel) < C := lt_of_le_of_ne hQC
    (by
      intro he
      apply hc
      change c ∈ (Q : Subgroup DerivedModel)
      rw [he]
      exact hcC)
  exact ⟨C.comap m.actor,isCoatom_comap_of_surjective m.actor_surjective
    (g2_sylow_overgroup Q C hC hQlt),hJC⟩

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
/-- Both literal maximal centralizers for an original local G₂ block. -/
theorem localFamily_g2_seed_centralizer
    (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hb : IsG2TwoBlock K) :
    d.MZ ⊓ K = K ⊓ centralizer (centralInvolutions T : Set G) ∧
      IsCoatom ((d.MZ ⊓ K).subgroupOf K) ∧
      d.MZ ⊓ K = K ⊓ centralizer
        (((blockU K).map K.subtype ⊓ centralizer (d.S ⊓ K : Set G) : Subgroup G) : Set G) := by
  apply d.localFamily_centralizing_of_small_fixers h hTM hu hK hq hout hb.short.fitting
    hb.central_sylow_fixers_card_le_two (g2_fixer_parabolic hb)
  obtain ⟨m⟩ := hb.natural_model
  exact inner_of_sylow_fixer hb.short hq m g2_action_injective

private theorem core_pair_marking {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (S₀ : Sylow 2 Y) (P R : Subgroup Y)
    (hgen : P ⊔ R = ⊤) (hSP : (S₀ : Subgroup Y) ≤ P) (hSR : (S₀ : Subgroup Y) ≤ R)
    (hinv : ∀ a : MulAut Y, (S₀ : Subgroup Y).map a.toMonoidHom = S₀ →
      P.map a.toMonoidHom = P ∧ R.map a.toMonoidHom = R)
    (hPm : IsCoatom P) (hRm : IsCoatom R)
    (hf : generalizedFitting X = pCore 2 X)
    (e : (X ⧸ pCore 2 X) ≃* Y) (S : Sylow 2 X) :
    ∃ (g : Y) (C E : Subgroup X), C ⊔ E = ⊤ ∧
      (S : Subgroup X) ≤ C ∧ (S : Subgroup X) ≤ E ∧
      generalizedFitting C = pCore 2 C ∧ generalizedFitting E = pCore 2 E ∧
      (∃ f : C →* P, Function.Surjective f ∧ IsPGroup 2 f.ker) ∧
      (∃ f : E →* R, Function.Surjective f ∧ IsPGroup 2 f.ker) ∧
      (∀ a : MulAut X, (S : Subgroup X).map a.toMonoidHom = S →
        C.map a.toMonoidHom = C ∧ E.map a.toMonoidHom = E) ∧
      IsCoatom C ∧ IsCoatom E ∧
      C.map ((MulAut.conj g).toMonoidHom.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X)))) = P ∧
      E.map ((MulAut.conj g).toMonoidHom.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X)))) = R := by
  let q₀ := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq₀ : Function.Surjective q₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let U := S.mapSurjective (f := q₀) hq₀
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Y U S₀
  let t := e.trans (MulAut.conj g)
  let q := t.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq : Function.Surjective q := t.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ _ t.injective,QuotientGroup.ker_mk']
  have hS : (S : Subgroup X).map q = S₀ := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((S : Subgroup X).map q₀).map (MulAut.conj g).toMonoidHom = _ at hh
    rw [map_map] at hh
    exact hh
  let C := P.comap q
  let E := R.comap q
  have hSC : (S : Subgroup X) ≤ C := (map_le_iff_le_comap).mp (hS ▸ hSP)
  have hSE : (S : Subgroup X) ≤ E := (map_le_iff_le_comap).mp (hS ▸ hSR)
  have hfit (D : Subgroup X) (hSD : (S : Subgroup X) ≤ D) :
      generalizedFitting D = pCore 2 D :=
    generalizedFitting_eq_pCore_of_normalized_by_pCore D hf
      ((pCore_isPGroup.le_sylow_of_normal S).trans (hSD.trans D.le_normalizer))
  have cover (P : Subgroup Y) :
      ∃ f : P.comap q →* P, Function.Surjective f ∧ IsPGroup 2 f.ker := by
    let f : P.comap q →* P := (q.comp (P.comap q).subtype).codRestrict P (fun x => x.property)
    have hfs : Function.Surjective f := by
      intro y
      obtain ⟨x,hx⟩ := hq y
      exact ⟨⟨x,show q x ∈ P from hx.symm ▸ y.property⟩,Subtype.ext hx⟩
    refine ⟨f,hfs,?_⟩
    have he : f.ker = q.ker.subgroupOf (P.comap q) := by
      ext x
      change (⟨q x,x.property⟩ : P) = 1 ↔ q x = 1
      exact Subtype.ext_iff
    rw [he,hk]
    exact pCore_isPGroup.comap_subtype
  refine ⟨g,C,E,?_,hSC,hSE,hfit C hSC,hfit E hSE,cover _,cover _,?_,?_,?_,?_,?_⟩
  · change P.comap q ⊔ R.comap q = ⊤
    rw [comap_sup_eq _ _ _ hq,hgen,comap_top]
  · intro a ha
    let b := MulAut.congr t (quotientAut (pCore 2 X) a)
    have he (x : X) : q (a x) = b (q x) := by
      change t (QuotientGroup.mk' (pCore 2 X) (a x)) =
        t (quotientAut (pCore 2 X) a (t.symm (t (QuotientGroup.mk' (pCore 2 X) x))))
      rw [t.symm_apply_apply,quotientAut_apply_mk]
    have hUb : (S₀ : Subgroup Y).map b.toMonoidHom = S₀ := by
      rw [←hS]
      have hhom : b.toMonoidHom.comp q = q.comp a.toMonoidHom := MonoidHom.ext (fun x => (he x).symm)
      rw [map_map,hhom,←map_map,ha]
    exact ⟨map_comap_equivariant q a b he _ (hinv b hUb).1,
      map_comap_equivariant q a b he _ (hinv b hUb).2⟩
  · exact isCoatom_comap_of_surjective hq
      hPm
  · exact isCoatom_comap_of_surjective hq
      hRm
  · exact map_comap_eq_self_of_surjective hq _
  · exact map_comap_eq_self_of_surjective hq _

omit [Finite G] in
private theorem ambient_coatom_eq (K : Subgroup G) (C : Subgroup K)
    (hC : IsCoatom C) (X : Subgroup G) (hX : X < K)
    (hle : C.map K.subtype ≤ X) : C.map K.subtype = X := by
  have hsub : C ≤ X.subgroupOf K := fun x hx => hle (mem_map_of_mem K.subtype hx)
  have hn : X.subgroupOf K ≠ ⊤ := by
    intro he
    have hh := congrArg (map K.subtype) he
    rw [map_subgroupOf_eq_of_le hX.le,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hX.ne hh
  have he := (hC.le_iff_eq hn).mp hsub
  have hh := congrArg (map K.subtype) he
  rw [map_subgroupOf_eq_of_le hX.le] at hh
  exact hh.symm

/-- Both G₂ parabolics are the literal original intersections under one
marking of the original two-core quotient. -/
theorem PreExclusionSource.constrained_g2_marked_parabolics
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* DerivedModel) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* DerivedModel,
      (∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∧
      ∃ g : DerivedModel,
        let q := (MulAut.conj g).toMonoidHom.comp
          (t.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L)))
        (((d.ML.subgroupOf d.L).map q = derivedFirst ∧
          ((M ⊓ d.L).subgroupOf d.L).map q = derivedSecond) ∨
         ((d.ML.subgroupOf d.L).map q = derivedSecond ∧
          ((M ⊓ d.L).subgroupOf d.L).map q = derivedFirst)) ∧
        d.IsSourceParabolic d.ML ∧ d.IsSourceParabolic (M ⊓ d.L) ∧
        IsCoatom (d.ML.subgroupOf d.L) ∧ IsCoatom ((M ⊓ d.L).subgroupOf d.L) ∧
        d.ML ≠ M ⊓ d.L ∧ (M ⊓ d.L) ⊔ d.ML = d.L := by
  have hK : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h
    hK s.quasisimple d.L_not_le_MZ hf
  let t := a.g2Derived_coreEquiv s.quasisimple e
  have hn := d.localFamily_g2_normalizes hG h hK s.quasisimple t
  obtain ⟨Q,hQ⟩ := s.component_sylow
  obtain ⟨g,C,E,hgen,hQC,hQE,hCf,hEf,⟨fC,hfC,hkC⟩,⟨fE,hfE,hkE⟩,
      hinv,hCmax,hEmax,hCm,hEm⟩ := core_pair_marking derivedSylow derivedFirst derivedSecond pair_generate
        derivedSylow_le_first derivedSylow_le_second pair_invariant
        (Atlas.G2.BinarySylowCenterMaximal.parabolic_isCoatom _ derivedSylow_le_first card_derivedFirst)
        (Atlas.G2.BinarySylowCenterMaximal.parabolic_isCoatom _ derivedSylow_le_second card_derivedSecond)
        hf t Q
  obtain ⟨hCP,_⟩ := lifted_source (H := derivedFirst) d Q hQ hn C hCf
    (fun a ha => (hinv a ha).1) firstPermQuotient derivedFirst_residual_not_exponent_six
    fC hfC hkC
  obtain ⟨hEP,_⟩ := lifted_source (H := derivedSecond) d Q hQ hn E hEf
    (fun a ha => (hinv a ha).2) secondPermQuotient derivedSecond_residual_not_exponent_six
    fE hfE hkE
  let P := C.map d.L.subtype
  let R := E.map d.L.subtype
  have hPR : P ⊔ R = d.L := by
    have hh := congrArg (map d.L.subtype) hgen
    simpa only [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] using hh
  have hplace := s.parabolic_placement_of_sylow_normalizes hG hM hJ hu h hn
  have hp : P ≤ M ⊓ d.L ∨ P ≤ d.ML := hplace P hCP
  have hr : R ≤ M ⊓ d.L ∨ R ≤ d.ML := hplace R hEP
  have hloc := s.local_intersections (h := h) hG hu hM.1.2
  have hpos : (d.ML = P ∧ M ⊓ d.L = R) ∨ (d.ML = R ∧ M ⊓ d.L = P) := by
    rcases hp with hp | hp <;> rcases hr with hr | hr
    · exact (not_le_of_gt hloc.2.2.2.2.1 (hPR.symm.le.trans (sup_le hp hr))).elim
    · exact Or.inr ⟨(ambient_coatom_eq d.L E hEmax d.ML hloc.2.2.1 hr).symm,
        (ambient_coatom_eq d.L C hCmax (M ⊓ d.L) hloc.2.2.2.2.1 hp).symm⟩
    · exact Or.inl ⟨(ambient_coatom_eq d.L C hCmax d.ML hloc.2.2.1 hp).symm,
        (ambient_coatom_eq d.L E hEmax (M ⊓ d.L) hloc.2.2.2.2.1 hr).symm⟩
    · exact (not_le_of_gt hloc.2.2.1 (hPR.symm.le.trans (sup_le hp hr))).elim
  have hPC : P.subgroupOf d.L = C := comap_map_eq_self (by
    rw [d.L.ker_subtype]; exact bot_le)
  have hRE : R.subgroupOf d.L = E := comap_map_eq_self (by
    rw [d.L.ker_subtype]; exact bot_le)
  have hne : P ≠ R := by
    intro he
    have hh : d.L ≤ d.ML := by
      rcases hpos with ⟨hm,_⟩ | ⟨hm,_⟩
      · rw [hm,←hPR,he,sup_idem]
      · rw [hm,←hPR,he,sup_idem]
    exact not_le_of_gt hloc.2.2.1 hh
  let q := (MulAut.conj g).toMonoidHom.comp
    (t.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L)))
  have hmP : (P.subgroupOf d.L).map q = derivedFirst := (congrArg (map q) hPC).trans hCm
  have hmR : (R.subgroupOf d.L).map q = derivedSecond := (congrArg (map q) hRE).trans hEm
  have images :
      (((d.ML.subgroupOf d.L).map q = derivedFirst ∧
        ((M ⊓ d.L).subgroupOf d.L).map q = derivedSecond) ∨
       ((d.ML.subgroupOf d.L).map q = derivedSecond ∧
        ((M ⊓ d.L).subgroupOf d.L).map q = derivedFirst)) := by
    have move (X Y : Subgroup G) (he : X = Y) :
        (X.subgroupOf d.L).map q = (Y.subgroupOf d.L).map q :=
      congrArg (fun B : Subgroup G => (B.subgroupOf d.L).map q) he
    exact hpos.elim
      (fun hh => Or.inl ⟨(move _ _ hh.1).trans hmP,(move _ _ hh.2).trans hmR⟩)
      (fun hh => Or.inr ⟨(move _ _ hh.1).trans hmR,(move _ _ hh.2).trans hmP⟩)
  refine ⟨t,fun k => a.g2Derived_coreEquiv_mk s.quasisimple e k,g,images,?_,?_,?_,?_,?_,?_⟩
  · exact hpos.elim (fun hh => hh.1.symm ▸ hCP) (fun hh => hh.1.symm ▸ hEP)
  · exact hpos.elim (fun hh => hh.2.symm ▸ hEP) (fun hh => hh.2.symm ▸ hCP)
  · rcases hpos with ⟨hm,_⟩ | ⟨hm,_⟩
    · rw [hm,hPC]; exact hCmax
    · rw [hm,hRE]; exact hEmax
  · rcases hpos with ⟨_,hn⟩ | ⟨_,hn⟩
    · rw [hn,hRE]; exact hEmax
    · rw [hn,hPC]; exact hCmax
  · rcases hpos with ⟨hm,hn⟩ | ⟨hm,hn⟩
    · rw [hm,hn]; exact hne
    · rw [hm,hn]; exact hne.symm
  · rcases hpos with ⟨hm,hn⟩ | ⟨hm,hn⟩
    · rw [hm,hn,sup_comm,hPR]
    · rw [hm,hn,hPR]

/-- The additional G₂ block clause for every actual C-component of the
original local family, with the full central attachment retained. -/
theorem PreExclusionSource.localComponent_g2_geometry
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hc : K ∈ Chapter1.cComponentsIn d.G1)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    (e : d.normalizerImage K ≃* DerivedModel) :
    IsG2TwoBlock K ∧
      (∃ t : (K ⧸ pCore 2 K) ≃* DerivedModel,
        ∀ k : K, t (QuotientGroup.mk' (pCore 2 K) k) = e (d.toNormalizerImage K k)) ∧
      d.MZ ⊓ K = K ⊓ centralizer (centralInvolutions T : Set G) ∧
      IsCoatom ((d.MZ ⊓ K).subgroupOf K) ∧
      d.MZ ⊓ K = K ⊓ centralizer
        (((blockU K).map K.subtype ⊓ centralizer (d.S ⊓ K : Set G) : Subgroup G) : Set G) := by
  obtain ⟨hb,ht⟩ := s.localComponent_g2_block (h := h) hG hempty hM hJ hu hK hc hq hout hf e
  exact ⟨hb,ht,d.localFamily_g2_seed_centralizer h hM.1.2 hu hK hq hout hb⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
open Atlas.G2.BinaryParabolicPair
variable {G : Type*} [Group G] [Finite G]

/-- The original marker supplies every G₂ block, centralizer and opposite
parabolic clause on its actual component. Earlier 15.1.14 remains explicit. -/
theorem PreparedChosenModule.source_preExclusion_constrained_g2_marked_geometry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        ∀ e : d.normalizerImage d.L ≃* DerivedModel,
          IsG2TwoBlock d.L ∧ Nat.card d.plusOmega = 2 ∧
          d.ML = d.L ⊓ centralizer (centralInvolutions T : Set G) ∧
          d.ML = d.L ⊓ centralizer
            (((blockU d.L).map d.L.subtype ⊓ centralizer (d.SL : Set G) : Subgroup G) : Set G) ∧
          d.ConstrainedCentralizerIdentity ∧
          ∃ t : (d.L ⧸ pCore 2 d.L) ≃* DerivedModel,
            (∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∧
            ∃ g : DerivedModel,
              let q := (MulAut.conj g).toMonoidHom.comp
                (t.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L)))
              (((d.ML.subgroupOf d.L).map q = derivedFirst ∧
                ((M ⊓ d.L).subgroupOf d.L).map q = derivedSecond) ∨
               ((d.ML.subgroupOf d.L).map q = derivedSecond ∧
                ((M ⊓ d.L).subgroupOf d.L).map q = derivedFirst)) ∧
              d.IsSourceParabolic d.ML ∧ d.IsSourceParabolic (M ⊓ d.L) ∧
              IsCoatom (d.ML.subgroupOf d.L) ∧ IsCoatom ((M ⊓ d.L).subgroupOf d.L) ∧
              d.ML ≠ M ⊓ d.L ∧ (M ⊓ d.L) ⊔ d.ML = d.L) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro hf e
  obtain ⟨hc,hb,hcent,_⟩ := s.constrained_g2 (h := h) hG hempty hM hJ hfull hu hf e
  obtain ⟨hseed,_,hfixed⟩ := d.localFamily_g2_seed_centralizer h hM.1.2 hu
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hb
  exact ⟨hb,hc,hseed,hfixed,hcent,
    s.constrained_g2_marked_parabolics (h := h) hG hempty hM hJ hu hf e⟩

namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Both exchanged plane sizes retain the G₂ full-core centralizers of the
same original component. No exchanged hypothesis enters the earlier proof. -/
theorem ExchangedSource.constrained_g2_block_centralizers
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (h : PreparedChosenModule T M V) (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hb : IsG2TwoBlock d.L) :
    d.ML = d.L ⊓ centralizer (centralInvolutions T : Set G) ∧
      IsCoatom (d.ML.subgroupOf d.L) ∧
      d.ML = d.L ⊓ centralizer
        (((blockU d.L).map d.L.subtype ⊓ centralizer (d.SL : Set G) : Subgroup G) : Set G) :=
  d.localFamily_g2_seed_centralizer h hM.1.2 hu
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hb

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
