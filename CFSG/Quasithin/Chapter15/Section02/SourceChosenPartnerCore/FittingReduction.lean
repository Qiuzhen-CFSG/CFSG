module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.PrimeComplement
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Inputs
public import Theory.GroupTheory.GeneralizedFitting.PrimeComplementResidual
public import Theory.GroupTheory.GeneralizedFitting.PreimageMovement
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.PCoreCentralQuotientImage
public import Theory.GroupTheory.PResidual.PrimeToPerfect
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.ConjugatePairInternalLift
/-!
# The partner Fitting and commutator reductions in 15.2.27

The embedded O₃′(Mc) containment and the literal equality Kc = O^{3′}(Mc)
put the entire preimage of F*(Mc/O₂(Mc)) in Kc(M ∩ Mc). This uses the
full generalized Fitting subgroup, including its ordinary components.

If V escapes O₂(Mc), its normality in M ∩ Mc forces nontrivial movement
of Kc even modulo O₂(Mc). The local-core comparison then excludes Kc = K.
In either remaining structural row, the image of Kc is a single T-orbit of
ordinary components. The component commutator dichotomy and two-perfectness
lift the full commutator equality back to the original embedded Kc.

Finally Mc = C_G(Z) makes the literal seed Z central. Even characteristic
and central-quotient descent give C_Mc(Qc/Z) ≤ Qc through the actual quotient
map. The entire seed is shown to lie in Qc, so the denominator is unchanged.

The explicit preceding inputs are 15.2.8, 15.2.12(2),(4), and, for the final
centralizer assertion, 15.2.14(1). These conclusions belong to their earlier
source owners. No result of 15.2.26 or partner-core containment is used.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.2.27(1) and the opening of (2), printed pp.1118--1119,
refs/quasithin.pdf pp.1135--1136.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChosenGeometry
variable {G : Type*} [Group G] [Finite G]

/-- Original 15.2.27(1), with the original Mc inclusion and two-core quotient. -/
theorem source_chosen_generalizedFitting_preimage_le
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc) :
    ((generalizedFitting (Mc ⧸ pCore 2 Mc)).comap
      (QuotientGroup.mk' (pCore 2 Mc))).map Mc.subtype ≤
        partnerSpan H Mc ⊔ (M ⊓ Mc) := by
  have hh := map_mono (f := Mc.subtype)
    (twoCore_generalizedFitting_preimage_le_three_residual (G := Mc))
  rw [Subgroup.map_sup, ← threePrimeResidual_eq, ← hres] at hh
  exact hh.trans (sup_le_sup_left (source_chosen_threePrimeCore_le h hg hquotient) _)

omit [Finite G] in
private theorem partner_le {H Mc : Subgroup G} (hH : H ≤ Mc) : partnerSpan H Mc ≤ Mc :=
  conjugateSpanBy_le_self ((map_subtype_le _).trans hH)

private theorem module_partner {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS) : V ≤ Mc :=
  (h.prepared.inside_core H hg.outside).trans ((twoCore_le H).trans hg.in_partner)

private theorem fitting_intrinsic {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc) :
    (generalizedFitting (Mc ⧸ pCore 2 Mc)).comap
      (QuotientGroup.mk' (pCore 2 Mc)) ≤
        (partnerSpan H Mc).subgroupOf Mc ⊔ (M ⊓ Mc).subgroupOf Mc := by
  rw [← subgroupOf_sup (partner_le hg.in_partner) inf_le_right]
  exact map_le_iff_le_comap.mp (source_chosen_generalizedFitting_preimage_le h hg hquotient hres)

private theorem module_normalizer {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS) :
    (M ⊓ Mc).subgroupOf Mc ≤ normalizer (V.subgroupOf Mc : Set Mc) := by
  rw [← subgroupOf_normalizer_eq (module_partner h hg)]
  exact comap_mono (inf_le_left.trans h.prepared.normalized)

private theorem noncore_intrinsic {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hne : ¬ V ≤ twoCoreIn Mc) : ¬ V.subgroupOf Mc ≤ pCore 2 Mc := by
  intro hh
  apply hne
  have hm := map_mono (f := Mc.subtype) hh
  rwa [map_subgroupOf_eq_of_le (module_partner h hg)] at hm

/-- Noncore V moves Kc even in Mc/O₂(Mc). -/
theorem source_chosen_noncore_commutator_not_le
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hne : ¬ V ≤ twoCoreIn Mc) : ¬ ⁅partnerSpan H Mc,V⁆ ≤ twoCoreIn Mc := by
  let := h.prepared.elementary
  let : ((partnerSpan H Mc).subgroupOf Mc).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  have hh := commutator_not_le_twoCore_of_preimage_le
    ((partnerSpan H Mc).subgroupOf Mc) ((M ⊓ Mc).subgroupOf Mc) (V.subgroupOf Mc)
    (fitting_intrinsic h hg hquotient hres)
    ((IsElementaryAbelian.isPGroup 2 V).comap_subtype)
    (comap_mono (le_inf h.prepared.le_selected (module_partner h hg)))
    (module_normalizer h hg) (noncore_intrinsic h hg hne)
  intro hc
  apply hh
  apply (map_le_map_iff_of_injective Mc.subtype_injective).mp
  rw [map_commutator, map_subgroupOf_eq_of_le (partner_le hg.in_partner),
    map_subgroupOf_eq_of_le (module_partner h hg)]
  exact hc

/-- The first commutator consequence in the noncore branch of 15.2.27(2). -/
theorem source_chosen_noncore_commutator_ne_bot
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hne : ¬ V ≤ twoCoreIn Mc) : ⁅partnerSpan H Mc,V⁆ ≠ ⊥ := by
  intro he
  exact source_chosen_noncore_commutator_not_le h hg hquotient hres hne (he ▸ bot_le)

/-- The unchanged local residual is strictly smaller than its partner span. -/
theorem source_chosen_noncore_residual_lt
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hne : ¬ V ≤ twoCoreIn Mc) : residual H < partnerSpan H Mc := by
  apply lt_of_le_of_ne (le_conjugateSpanBy _ _)
  intro he
  change residual H = partnerSpan H Mc at he
  let : ((partnerSpan H Mc).subgroupOf Mc).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  apply noncore_intrinsic h hg hne
  apply le_twoCore_of_preimage_le_of_local_core
    ((partnerSpan H Mc).subgroupOf Mc) ((M ⊓ Mc).subgroupOf Mc)
    (V.subgroupOf Mc) (H.subgroupOf Mc) (fitting_intrinsic h hg hquotient hres)
    (comap_mono (le_inf h.prepared.le_selected (module_partner h hg))) (module_normalizer h hg)
  · apply comap_mono
    rw [← he]
    exact map_subtype_le (pResidual 2 H)
  · rw [pCoreIn_subgroupOf 2 H Mc hg.in_partner]
    exact comap_mono (h.prepared.inside_core H hg.outside)

private theorem model_quasisimple {X : Type*} [Group X] [Group.IsPerfect X]
    {n q : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL X n q) : IsQuasisimple X := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := hm
  have hs : IsSimpleGroup X := by
    by_cases he : n = 2
    · subst n
      let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
        Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      have hh : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
        MulAction.IwasawaStructure.isSimpleGroup Group.IsPerfect.commutator_eq_top
          PSL2.Iwasawa inferInstance
      exact e.isSimpleGroup_congr.mpr hh
    · let := Atlas.psl_simple_high_rank (F := F) n (by omega)
      exact e.isSimpleGroup
  let := hs
  have hz : center X = ⊥ := (inferInstance : (center X).Normal).eq_bot_or_eq_top.resolve_right
    (fun he => Group.IsPerfect.not_isMulCommutative X (center_eq_top_iff.mp he))
  exact { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup }

private theorem component_image {L Mc : Subgroup G}
    (hL : L ∈ Chapter1.cComponentsIn Mc) (hq : IsQuasisimple (Chapter1.XiQuotient L)) :
    IsComponent (Mc ⧸ pCore 2 Mc)
      ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) := by
  let e := subgroupOfEquivOfLe hL.1
  let eQ := QuotientGroup.congr (pCore 2 (L.subgroupOf Mc)) (pCore 2 L)
    e (pCore_map_iso 2 e)
  let := hq
  let : IsQuasisimple ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) :=
    IsQuasisimple.of_mulEquiv (eQ.symm.trans (cComponentTwoCoreQuotientEquiv hL.2))
  exact ⟨hL.2.subnormal.quotient, inferInstance⟩

omit [Finite G] in
private theorem perfect_component {L Mc : Subgroup G}
    (hL : L ∈ Chapter1.cComponentsIn Mc) : Group.IsPerfect (Chapter1.XiQuotient L) := by
  let := hL.2.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hL.1).toMonoidHom) (subgroupOfEquivOfLe hL.1).surjective
  exact Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (pCore 2 L))

private theorem source_component_orbit
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hlt : residual H < partnerSpan H Mc) (hs : StructuralAlternatives T H Mc) :
    ∃ L : Subgroup (Mc ⧸ pCore 2 Mc), IsComponent (Mc ⧸ pCore 2 Mc) L ∧
      ((partnerSpan H Mc).subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc)) =
        ⨆ a : ((T : Subgroup G).subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc)),
          L.map (MulAut.conj (a : Mc ⧸ pCore 2 Mc)).toMonoidHom := by
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let K := (partnerSpan H Mc).subgroupOf Mc
  let A := ((T : Subgroup G).subgroupOf Mc).map q
  let : K.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  have hn : A ≤ normalizer (K.map q : Set (Mc ⧸ pCore 2 Mc)) := le_normalizer_of_normal
  rcases hs with he | ⟨_, hc, n, hn, hm, _⟩ | ⟨L,t,_,hc,ht,_,he,_,hm⟩
  · exact (hlt.ne he.symm).elim
  · let := perfect_component hc
    have hq := model_quasisimple (by rcases hn with rfl | rfl <;> decide) hm
    refine ⟨K.map q, component_image hc hq, ?_⟩
    exact le_antisymm (le_iSup_conjugates _ _)
      (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl le_normalizer_of_normal)
  · let := perfect_component hc
    have hq : IsQuasisimple (Chapter1.XiQuotient L) := by
      rcases hm with ⟨n,_,hm⟩ | ⟨p,_,_,hm⟩
      · exact model_quasisimple (by decide) hm
      · exact model_quasisimple (by decide) hm
    let B := (L.subgroupOf Mc).map q
    have hTMc := hg.outside.1.1.2.trans hg.in_partner
    let tM : Mc := ⟨t,hTMc ht⟩
    have hct : L.conjBy t ≤ Mc := (map_mono hc.1).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (Mc.le_normalizer (hTMc ht)))
    have hcj : (L.conjBy t).subgroupOf Mc = (L.subgroupOf Mc).conjBy tM := by
      apply Subgroup.map_injective Mc.subtype_injective
      rw [map_subgroupOf_eq_of_le hct, map_conjBy_hom, map_subgroupOf_eq_of_le hc.1]
      rfl
    have hpair : K.map q = B ⊔ B.conjBy (q tM) := by
      change ((partnerSpan H Mc).subgroupOf Mc).map q = _
      rw [he, subgroupOf_sup hc.1 hct, Subgroup.map_sup, hcj, map_conjBy_hom]
    have hBK : B ≤ K.map q := hpair ▸ le_sup_left
    refine ⟨B, component_image hc hq, le_antisymm ?_ ?_⟩
    · rw [hpair]
      exact sup_le (le_iSup_conjugates B A)
        (le_iSup (fun a : A => B.map (MulAut.conj (a : Mc ⧸ pCore 2 Mc)).toMonoidHom)
          ⟨q tM, mem_map_of_mem q ht⟩)
    · exact iSup_conjugates_le_of_le_normalizer B A (K.map q) hBK hn

/-- The full source commutator conclusion, in both noncore structural rows. -/
theorem source_chosen_noncore_eq_commutator
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc) (hne : ¬ V ≤ twoCoreIn Mc) :
    partnerSpan H Mc = ⁅partnerSpan H Mc,V⁆ := by
  let := h.prepared.elementary
  let K := (partnerSpan H Mc).subgroupOf Mc
  let : K.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  have hK : IsPPerfect 2 K := by
    have he : K = primeToResidual 3 Mc := by
      change (partnerSpan H Mc).subgroupOf Mc = _
      rw [hres, threePrimeResidual_eq]
      exact comap_map_eq_self_of_injective Mc.subtype_injective _
    rw [he]
    exact isPPerfect_primeToResidual 3 2 (by decide)
  have hAV : (T : Subgroup G).subgroupOf Mc ≤ normalizer (V.subgroupOf Mc : Set Mc) := by
    rw [← subgroupOf_normalizer_eq (module_partner h hg)]
    exact comap_mono (h.maximal.1.2.trans h.prepared.normalized)
  have he := commutator_eq_of_component_orbit_image K ((M ⊓ Mc).subgroupOf Mc)
    (V.subgroupOf Mc) ((T : Subgroup G).subgroupOf Mc)
    (fitting_intrinsic h hg hquotient hres) hK
    ((IsElementaryAbelian.isPGroup 2 V).comap_subtype)
    (comap_mono (le_inf h.prepared.le_selected (module_partner h hg)))
    (module_normalizer h hg) hAV (noncore_intrinsic h hg hne)
    (source_component_orbit h hg (source_chosen_noncore_residual_lt h hg hquotient hres hne) hs)
  have hm := congrArg (Subgroup.map Mc.subtype) he
  rw [map_commutator, map_subgroupOf_eq_of_le (module_partner h hg),
    map_subgroupOf_eq_of_le (partner_le hg.in_partner)] at hm
  exact hm.symm

/-- The source denominator is central in the actual partner. -/
theorem source_chosen_seed_central
    {T : Sylow 2 G} {M Mc V : Subgroup G} (_h : ChosenSmallSource T M Mc V)
    (hMc : Mc = centralizer (centralInvolutions T : Set G)) :
    (centralInvolutions T).subgroupOf Mc ≤ center Mc := by
  intro z hz
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact ((show (x : G) ∈ centralizer (centralInvolutions T : Set G) from hMc ▸ x.property)
    z hz).symm

/-- Relative normality for the literal quotient Mc/Z. -/
theorem source_chosen_seed_normal
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hMc : Mc = centralizer (centralInvolutions T : Set G)) :
    ((centralInvolutions T).subgroupOf Mc).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  calc
    ⊤ = centralizer (center Mc : Set Mc) := centralizer_center.symm
    _ ≤ centralizer ((centralInvolutions T).subgroupOf Mc : Set Mc) :=
      centralizer_le (source_chosen_seed_central h hMc)
    _ ≤ normalizer ((centralInvolutions T).subgroupOf Mc : Set Mc) :=
      Subgroup.centralizer_le_normalizer _

private theorem partner_characteristicTwo
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS) :
    centralizer (pCore 2 Mc : Set Mc) ≤ pCore 2 Mc := by
  have hmax : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := h.partner ▸ Set.mem_singleton _
  exact h.ambient.evenCharacteristic T Mc hmax.1
    (hg.outside.1.1.2.trans hg.in_partner)

/-- The entire seed, and therefore the literal denominator Z, lies in Qc. -/
theorem source_chosen_seed_le_partner_twoCore
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G)) :
    centralInvolutions T ≤ twoCoreIn Mc := by
  have hZM := (centralInvolutions_le_sylow T).trans
    (hg.outside.1.1.2.trans hg.in_partner)
  have hh := (source_chosen_seed_central h hMc).trans
    ((center_le_centralizer _).trans (partner_characteristicTwo h hg))
  have hm := map_mono (f := Mc.subtype) hh
  rwa [map_subgroupOf_eq_of_le hZM] at hm

/-- A.1.8 on Mc/Z: the full preimage of the centralizer of Qc/Z lies in Qc.
Both images use the original quotient homomorphism and the inclusion Mc → G. -/
theorem source_chosen_core_quotient_centralizer
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G)) :
    let Z := (centralInvolutions T).subgroupOf Mc
    let : Z.Normal := source_chosen_seed_normal h hMc
    let q := QuotientGroup.mk' Z
    ((centralizer ((pCore 2 Mc).map q : Set (Mc ⧸ Z))).comap q).map Mc.subtype ≤
      twoCoreIn Mc := by
  dsimp only
  let Z := (centralInvolutions T).subgroupOf Mc
  let : Z.Normal := source_chosen_seed_normal h hMc
  have hZ : Z ≤ center Mc := source_chosen_seed_central h hMc
  have hc := partner_characteristicTwo h hg
  have hZQ : Z ≤ pCore 2 Mc := (hZ.trans (center_le_centralizer _)).trans hc
  have hh := comap_mono (f := QuotientGroup.mk' Z)
    (centralizer_image_pCore_le_of_central_quotient Z hZ hc)
  rw [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hZQ] at hh
  exact map_mono hh

end CFSG.Quasithin.Chapter15.Section02
