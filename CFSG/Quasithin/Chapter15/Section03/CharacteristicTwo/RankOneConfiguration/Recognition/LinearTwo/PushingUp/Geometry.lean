module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.PushingUp.Borel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.PushingUp.Reduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.Quotient
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Lifting the marked Borel to the local groups I and LR

The actual marking of M ∩ L identifies the image of L ∩ S with the upper
root group of SL₂. The map from L factors through L/O₂(L); quasisimplicity
makes the remaining kernel central. Centrality lifts the Sylow normalizer,
while perfectness ensures that a proper subgroup containing a Sylow subgroup
still has proper image. Thus the marked Borel controls both normalization
and all proper overgroups of L ∩ S, without identifying the star kernel
with O₂(L).

It follows that Y₊ normalizes L ∩ S and that R = O₂(Y₊S) is the image of a
Sylow subgroup of LR. For J = LD with L ∩ S ≤ D ≤ S, a subgroup K containing
D decomposes as (K ∩ L)D. Hence every proper such K lies in M ∩ J. Applying
this with D = S and D = R proves B.6.1 for both I and LR. Nonnormality is
detected by the nonnormal upper root group in the linear image.

The only extra local clause beyond `Earlier`, the component witness, and
the marked Borel is 15.3.11(2), C_I(U_I) ≤ M_I. The source theorem's assembly
owner supplies these preceding conclusions; no block recognition or
minimal-parabolic hypothesis is used here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Definition
B.6.1, printed p.112; 15.3.11, pp.1123–1124; and 15.3.26–30, pp.1130–1132.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp.Geometry

private theorem central_normalizer_lift {A B : Type*} [Group A] [Finite A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) (hc : f.ker ≤ center A)
    (P : Sylow 2 A) :
    (normalizer ((P : Subgroup A).map f : Set B)).comap f ≤
      normalizer (P : Set A) := by
  let N := ((P : Subgroup A).map f).comap f
  have hPN : (P : Subgroup A) ≤ N := le_comap_map f _
  have hn : N ≤ normalizer (P : Set A) := by
    change ((P : Subgroup A).map f).comap f ≤ _
    rw [comap_map_eq]
    exact sup_le (P : Subgroup A).le_normalizer
      (hc.trans (center_le_normalizer _))
  let Q := P.subtype hPN
  have hQn : (Q : Subgroup N).Normal :=
    (normal_subgroupOf_iff_le_normalizer hPN).mpr hn
  let : (Q : Subgroup N).Characteristic := Q.characteristic_of_normal hQn
  have he : (Q : Subgroup N).map N.subtype = (P : Subgroup A) :=
    map_subgroupOf_eq_of_le hPN
  rw [comap_normalizer_eq_of_surjective _ hf]
  change normalizer (N : Set A) ≤ _
  simpa only [he, Sylow.coe_coe] using normalizer_le_normalizer_characteristic_image N (Q : Subgroup N)

private theorem core_central_normalizer_lift {A B : Type*} [Group A] [Finite A] [Group B]
    (f : (A ⧸ pCore 2 A) →* B) (hf : Function.Surjective f)
    (hc : f.ker ≤ center (A ⧸ pCore 2 A)) (P : Sylow 2 A) :
    (normalizer ((P : Subgroup A).map
      (f.comp (QuotientGroup.mk' (pCore 2 A))) : Set B)).comap
      (f.comp (QuotientGroup.mk' (pCore 2 A))) ≤ normalizer (P : Set A) := by
  let q := QuotientGroup.mk' (pCore 2 A)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker ≤ (P : Subgroup A) := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal P
  have h := comap_mono (f := q) (central_normalizer_lift f hf hc (P.mapSurjective hq))
  change ((normalizer (((P : Subgroup A).map q).map f : Set B)).comap f).comap q ≤
    (normalizer ((P : Subgroup A).map q : Set (A ⧸ pCore 2 A))).comap q at h
  rw [comap_normalizer_eq_of_surjective _ hq, comap_map_eq_self hker] at h
  simpa only [map_map, comap_comap, Sylow.coe_coe] using h

private theorem core_central_proper_image {A B : Type*} [Group A] [Group B]
    [Group.IsPerfect (A ⧸ pCore 2 A)]
    (f : (A ⧸ pCore 2 A) →* B) (hc : f.ker ≤ center (A ⧸ pCore 2 A))
    (H : Subgroup A) (hcore : pCore 2 A ≤ H) (hH : H ≠ ⊤) :
    H.map (f.comp (QuotientGroup.mk' (pCore 2 A))) ≠ ⊤ := by
  intro he
  let q := QuotientGroup.mk' (pCore 2 A)
  have hcomp : Function.Surjective (f.comp (q.comp H.subtype)) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, MonoidHom.range_comp, range_subtype]
    simpa only [map_map] using he
  have hsurj := PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
    f (q.comp H.subtype) hcomp hc
  have heq : H.map q = ⊤ := by
    simpa only [MonoidHom.range_comp, range_subtype] using
      MonoidHom.range_eq_top.mpr hsurj
  have hk : q.ker ≤ H := by simpa only [q, QuotientGroup.ker_mk'] using hcore
  apply hH
  have heq' := congrArg (Subgroup.comap q) heq
  simpa only [comap_map_eq_self hk, comap_top] using heq'

variable {G : Type*} [Group G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I} {n : ℕ} {F : Type*} [Field F] [Finite F] [CharP F 2]

private noncomputable def linearMap (b : BorelIdentification d I c n F) :
    c.L →* Matrix.SpecialLinearGroup (Fin 2) F :=
  b.linear.toMonoidHom.comp (SmallExtension.componentMap d c)

private theorem linearMap_surjective (b : BorelIdentification d I c n F) :
    Function.Surjective (linearMap b) :=
  b.linear.surjective.comp (SmallExtension.componentMap_surjective d c)

private noncomputable def coreLinearMap (b : BorelIdentification d I c n F)
    (h : Earlier d I c) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S) :
    (c.L ⧸ pCore 2 c.L) →* Matrix.SpecialLinearGroup (Fin 2) F :=
  b.linear.toMonoidHom.comp (QuotientGroup.lift (pCore 2 c.L)
    (SmallExtension.componentMap d c) (SmallExtension.core_le_componentMap_ker d c
      (SmallExtension.component_core_centralizes_span d c h.component_normal P hP)))

private theorem coreLinearMap_comp (b : BorelIdentification d I c n F)
    (h : Earlier d I c) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S) :
    (coreLinearMap b h P hP).comp (QuotientGroup.mk' (pCore 2 c.L)) = linearMap b := by
  ext x
  rfl

private theorem coreLinearMap_surjective (b : BorelIdentification d I c n F)
    (h : Earlier d I c) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S) :
    Function.Surjective (coreLinearMap b h P hP) := by
  intro x
  obtain ⟨l, hl⟩ := linearMap_surjective b x
  exact ⟨QuotientGroup.mk' (pCore 2 c.L) l, hl⟩

private theorem coreLinearMap_ker_central (b : BorelIdentification d I c n F)
    (h : Earlier d I c) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S) :
    (coreLinearMap b h P hP).ker ≤ center (c.L ⧸ pCore 2 c.L) := by
  let : Theory.GroupTheory.IsQuasisimple (c.L ⧸ pCore 2 c.L) := c.core_quotient_quasisimple
  rcases Theory.GroupTheory.IsQuasisimple.normal_le_center_or_eq_top
    (coreLinearMap b h P hP).ker with hc | ht
  · exact hc
  · have hn : Nontrivial (d.starImage I c.L) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr (component_star_ne_bot d c)
    let : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) := b.linear.symm.surjective.nontrivial
    obtain ⟨a, ha⟩ := exists_ne (1 : Matrix.SpecialLinearGroup (Fin 2) F)
    obtain ⟨x, rfl⟩ := coreLinearMap_surjective b h P hP a
    exact (ha (MonoidHom.mem_ker.mp (ht.ge (mem_top x)))).elim

private theorem intersection_linearMap (b : BorelIdentification d I c n F) :
    (d.M.subgroupOf c.L).map (linearMap b) = Matrix.SpecialLinearGroup.rankOneBorel F := by
  have hm : (d.M.subgroupOf c.L).map (SmallExtension.componentMap d c) =
      (d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L) := by
    apply le_antisymm
    · rintro _ ⟨l, hl, rfl⟩
      exact ⟨⟨l, component_le c l.property⟩, ⟨hl, l.property⟩, rfl⟩
    · rintro ⟨x, hx⟩ ⟨l, hl, he⟩
      exact ⟨⟨l, hl.2⟩, hl.1, Subtype.ext he⟩
  rw [linearMap, ← map_map, hm]
  exact b.linear_borel

private theorem exists_component_sylow [Finite G] (h : Earlier d I c) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S) :
    ∃ T : Sylow 2 c.L, (T : Subgroup c.L) = d.S.subgroupOf c.L := by
  let : (c.L.subgroupOf I).Normal := h.component_normal
  obtain ⟨T, hT⟩ := P.exists_subgroupOf_eq_of_normal (c.L.subgroupOf I)
  let e := subgroupOfEquivOfLe (component_le c)
  refine ⟨T.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (T : Subgroup (c.L.subgroupOf I)).map e.toMonoidHom = _
  ext l
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxP : (x : I) ∈ (P : Subgroup I) := by
      change x ∈ (P : Subgroup I).subgroupOf (c.L.subgroupOf I)
      rwa [← hT]
    exact hP ▸ mem_map_of_mem I.subtype hxP
  · intro hl
    obtain ⟨x, hx, hxl⟩ := hP.symm ▸ hl
    change (x : G) = (l : G) at hxl
    have hxL : (x : G) ∈ c.L := by rw [hxl]; exact l.property
    refine ⟨⟨x, hxL⟩, by rw [hT]; exact hx, ?_⟩
    exact Subtype.ext hxl

private theorem component_sylow_image [Finite G] (b : BorelIdentification d I c n F)
    (T : Sylow 2 c.L) (hT : (T : Subgroup c.L) = d.S.subgroupOf c.L) :
    (T : Subgroup c.L).map (linearMap b) = Matrix.SpecialLinearGroup.upperUnipotent F := by
  apply sylow_in_borel_eq_upper (T.mapSurjective (linearMap_surjective b))
  change (T : Subgroup c.L).map (linearMap b) ≤ _
  rw [← intersection_linearMap b]
  apply map_mono
  rw [hT]
  exact comap_mono (inf_le_left.trans d.sylow_le)

private theorem borel_normalizes_component_sylow [Finite G] (b : BorelIdentification d I c n F)
    (h : Earlier d I c) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (T : Sylow 2 c.L) (hT : (T : Subgroup c.L) = d.S.subgroupOf c.L) :
    d.M.subgroupOf c.L ≤ normalizer (T : Set c.L) := by
  have hlift := core_central_normalizer_lift (coreLinearMap b h P hP)
    (coreLinearMap_surjective b h P hP) (coreLinearMap_ker_central b h P hP) T
  rw [coreLinearMap_comp, component_sylow_image b T hT] at hlift
  apply le_trans ?_ hlift
  exact map_le_iff_le_comap.mp (intersection_linearMap b).le

/-- The marked Borel and central-kernel lift make Y₊ normalize L ∩ S in G. -/
theorem yplus_normalizes_intersection [Finite G] (b : BorelIdentification d I c n F)
    (h : Earlier d I c) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S) :
    d.Yplus ≤ normalizer ((c.L ⊓ d.S : Subgroup G) : Set G) := by
  obtain ⟨T, hT⟩ := exists_component_sylow h P hP
  have hn := (map_mono (f := c.L.subtype) (borel_normalizes_component_sylow b h P hP T hT)).trans
    ((T : Subgroup c.L).le_normalizer_map c.L.subtype)
  simp only [hT, subgroupOf_map_subtype] at hn
  rw [inf_comm d.S c.L] at hn
  apply le_trans ?_ hn
  exact le_inf ((h.theta_eq ▸ theta_le (d.MI I)).trans inf_le_left) h.contains

private theorem linearMap_ker_le_intersection (b : BorelIdentification d I c n F)
    (hc : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I) :
    (linearMap b).ker ≤ d.M.subgroupOf c.L := by
  intro x hx
  have hx' : SmallExtension.componentMap d c x = 1 :=
    b.linear.injective ((MonoidHom.mem_ker.mp hx).trans b.linear.map_one.symm)
  have hq : d.starMap I ⟨x, component_le c x.property⟩ = 1 :=
    congrArg Subtype.val hx'
  have hz : (x : G) ∈ centralizer (d.UI I : Set G) :=
    (QuotientGroup.eq_one_iff (N := localActionKernel d.Z I)
      (⟨x, component_le c x.property⟩ : I)).mp hq
  exact (hc ⟨component_le c x.property, hz⟩).1

private theorem component_proper_overgroup_le_intersection [Finite G]
    (b : BorelIdentification d I c n F) (h : Earlier d I c) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (hc : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    (T : Sylow 2 c.L) (hT : (T : Subgroup c.L) = d.S.subgroupOf c.L)
    (H : Subgroup c.L) (hTH : (T : Subgroup c.L) ≤ H) (hH : H ≠ ⊤) :
    H ≤ d.M.subgroupOf c.L := by
  let : Theory.GroupTheory.IsQuasisimple (c.L ⧸ pCore 2 c.L) := c.core_quotient_quasisimple
  have himage := core_central_proper_image (coreLinearMap b h P hP)
    (coreLinearMap_ker_central b h P hP) H
    ((pCore_isPGroup.le_sylow_of_normal T).trans hTH) hH
  rw [coreLinearMap_comp] at himage
  have hu : Matrix.SpecialLinearGroup.upperUnipotent F ≤ H.map (linearMap b) :=
    (component_sylow_image b T hT).symm.le.trans (map_mono hTH)
  have hb := proper_overgroup_upper_le_borel (H.map (linearMap b)) hu himage
  rw [← intersection_linearMap b, map_le_iff_le_comap,
    comap_map_eq_self (linearMap_ker_le_intersection b hc)] at hb
  exact hb

private theorem component_sylow_not_normal [Finite G]
    (b : BorelIdentification d I c n F)
    (T : Sylow 2 c.L) (hT : (T : Subgroup c.L) = d.S.subgroupOf c.L) :
    ¬ (T : Subgroup c.L).Normal := by
  intro hn
  have hn' := hn.map (linearMap b) (linearMap_surjective b)
  rw [component_sylow_image b T hT] at hn'
  exact Matrix.SpecialLinearGroup.upperUnipotent_not_normal F hn'

private theorem sylow_subgroupOf_eq (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S) :
    d.S.subgroupOf I = (P : Subgroup I) := by
  rw [← hP]
  exact comap_map_eq_self_of_injective I.subtype_injective _

/-- The same normalization statement inside I, with its actual Sylow P. -/
theorem yplus_normalizes_intersection_in_I [Finite G]
    (b : BorelIdentification d I c n F) (h : Earlier d I c) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S) :
    d.Yplus.subgroupOf I ≤ normalizer
      ((c.L.subgroupOf I ⊓ (P : Subgroup I) : Subgroup I) : Set I) := by
  have he : (c.L ⊓ d.S).subgroupOf I = c.L.subgroupOf I ⊓ (P : Subgroup I) := by
    change (c.L ⊓ d.S).comap I.subtype = _
    rw [comap_inf]
    exact congrArg (fun X => c.L.subgroupOf I ⊓ X) (sylow_subgroupOf_eq P hP)
  rw [← he, ← subgroupOf_normalizer_eq (h := inf_le_left.trans (component_le c))]
  exact comap_mono (yplus_normalizes_intersection b h P hP)

/-- Construct the Sylow subgroup of LR whose ambient image is R = O₂(Y₊S). -/
theorem exists_sylow_LR [Finite G]
    (b : BorelIdentification d I c n F) (h : Earlier d I c)
    (hI : I ∈ d.HplusMinimal) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S) :
    ∃ Q : Sylow 2 ↥(c.L ⊔ d.R),
      (Q : Subgroup ↥(c.L ⊔ d.R)).map (c.L ⊔ d.R).subtype = d.R := by
  have hLI := component_le c
  have hSI : d.S ≤ I := hP ▸ map_subtype_le (P : Subgroup I)
  have hYI : d.Yplus ≤ I := h.contains.trans hLI
  have hYM : d.Yplus ≤ d.M := (h.theta_eq ▸ theta_le (d.MI I)).trans inf_le_left
  have hgen := (lemma_15_3_27_4_of_containment d hI c P hP h.contains hYM).1
  have hgenI : c.L.subgroupOf I ⊔ (P : Subgroup I) = ⊤ := by
    rw [← sylow_subgroupOf_eq P hP, ← subgroupOf_sup hLI hSI, ← hgen,
      subgroupOf_self]
  let : (c.L.subgroupOf I).Normal := h.component_normal
  obtain ⟨Q, hQ⟩ := sylow_core_join_of_normalizes_intersection P (c.L.subgroupOf I)
    (d.Yplus.subgroupOf I) hgenI (yplus_normalizes_intersection_in_I b h P hP)
  let R' := (d.Yplus.subgroupOf I ⊔ (P : Subgroup I)).pCoreIn 2
  let J := c.L.subgroupOf I ⊔ R'
  have hR : R'.map I.subtype = d.R := by
    rw [map_pCoreIn_of_injective 2 _ I.subtype I.subtype_injective,
      Subgroup.map_sup, map_subgroupOf_eq_of_le hYI, hP]
  have hJ : J.map I.subtype = c.L ⊔ d.R := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hLI, hR]
  let e : J ≃* ↥(c.L ⊔ d.R) :=
    (J.equivMapOfInjective I.subtype I.subtype_injective).trans (MulEquiv.subgroupCongr hJ)
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((Q : Subgroup J).map e.toMonoidHom).map (c.L ⊔ d.R).subtype = _
  rw [map_map]
  have he : (c.L ⊔ d.R).subtype.comp e.toMonoidHom = I.subtype.comp J.subtype := rfl
  rw [he, ← map_map, hQ, hR]

private theorem proper_supplement_overgroup_le_M [Finite G]
    (b : BorelIdentification d I c n F) (h : Earlier d I c) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (hc : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    {D J K : Subgroup G} (hDS : D ≤ d.S) (hTD : c.L ⊓ d.S ≤ D)
    (hgen : J = c.L ⊔ D) (hDK : D ≤ K) (hK : K < J) : K ≤ d.M := by
  obtain ⟨T, hT⟩ := exists_component_sylow h P hP
  have hTH : (T : Subgroup c.L) ≤ K.subgroupOf c.L := by
    rw [hT]
    exact fun x hx => hDK (hTD ⟨x.property, hx⟩)
  have hH : K.subgroupOf c.L ≠ ⊤ := by
    intro he
    have hLK : c.L ≤ K := subgroupOf_eq_top.mp he
    exact hK.not_ge (hgen ▸ sup_le hLK hDK)
  have hsmall := component_proper_overgroup_le_intersection b h P hP hc T hT
    (K.subgroupOf c.L) hTH hH
  have hSI : d.S ≤ I := hP ▸ map_subtype_le (P : Subgroup I)
  have hnorm : D ≤ normalizer (c.L : Set G) := (hDS.trans hSI).trans
    ((normal_subgroupOf_iff_le_normalizer (component_le c)).mp h.component_normal)
  intro x hx
  have hxJ : x ∈ c.L ⊔ D := hgen ▸ hK.le hx
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left c.L D hnorm] at hxJ
  obtain ⟨l, hl, r, hr, he⟩ := hxJ
  have hlK : l ∈ K := by
    have hz := K.mul_mem hx (K.inv_mem (hDK hr))
    simpa only [← he, mul_inv_cancel_right] using hz
  rw [← he]
  exact d.M.mul_mem (hsmall (show (⟨l, hl⟩ : c.L) ∈ K.subgroupOf c.L from hlK))
    (d.sylow_le (hDS hr).1)

private theorem minimalParabolic_supplement [Finite G]
    (b : BorelIdentification d I c n F) (h : Earlier d I c) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (hc : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    {D J : Subgroup G} (hDS : D ≤ d.S) (hTD : c.L ⊓ d.S ≤ D)
    (hgen : J = c.L ⊔ D) (Q : Sylow 2 J)
    (hQ : (Q : Subgroup J).map J.subtype = D) :
    ChapterB.IsMinimalParabolicOver Q ⊤ := by
  have hLJ : c.L ≤ J := hgen ▸ le_sup_left
  have hDJ : D ≤ J := hgen ▸ le_sup_right
  have hB : d.M.subgroupOf J ≠ ⊤ := fun he =>
    c.outside (hLJ.trans (subgroupOf_eq_top.mp he))
  have hQB : (Q : Subgroup J) ≤ d.M.subgroupOf J := by
    intro x hx
    exact d.sylow_le (hDS (hQ ▸ mem_map_of_mem J.subtype hx)).1
  have hproper (K : Subgroup J) (hQK : (Q : Subgroup J) ≤ K) (hK : K ≠ ⊤) :
      K ≤ d.M.subgroupOf J := by
    have hKJ : K.map J.subtype < J := lt_of_le_of_ne (map_subtype_le K) (by
      intro he
      apply hK
      have hh := congrArg (Subgroup.comap J.subtype) he
      rw [comap_map_eq_self_of_injective J.subtype_injective] at hh
      change K = J.subgroupOf J at hh
      simpa only [subgroupOf_self] using hh)
    have hDK : D ≤ K.map J.subtype := hQ ▸ map_mono hQK
    have hm := proper_supplement_overgroup_le_M b h P hP hc hDS hTD hgen hDK hKJ
    exact fun x hx => hm (mem_map_of_mem J.subtype hx)
  have hcoatom : IsCoatom (d.M.subgroupOf J) :=
    isCoatom_iff_ge_of_le.mpr ⟨hB, fun K hK hBK => hproper K (hQB.trans hBK) hK⟩
  apply (ChapterB.isMinimalParabolicOver_top_iff Q).mpr
  refine ⟨⟨d.M.subgroupOf J, ⟨hcoatom, hQB⟩, ?_⟩, ?_⟩
  · intro K hK
    have hle := hproper K hK.2 hK.1.ne_top
    exact le_antisymm hle ((isCoatom_iff_ge_of_le.mp hK.1).2 _ hB hle)
  · intro hn
    obtain ⟨T, hT⟩ := exists_component_sylow h P hP
    have hD : D.subgroupOf J = (Q : Subgroup J) := by
      rw [← hQ]
      exact comap_map_eq_self_of_injective J.subtype_injective _
    have he : (Q : Subgroup J).comap (Subgroup.inclusion hLJ) = (T : Subgroup c.L) := by
      rw [← hD, hT]
      ext x
      exact ⟨fun hx => hDS hx, fun hx => hTD ⟨x.property, hx⟩⟩
    exact component_sylow_not_normal b T hT (he ▸ hn.comap (Subgroup.inclusion hLJ))

/-- The two-core R of Y₊S lies in the actual Sylow subgroup S. -/
theorem R_le_S (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (hYI : d.Yplus ≤ I) : d.R ≤ d.S := by
  have hSI : d.S ≤ I := hP ▸ map_subtype_le (P : Subgroup I)
  let YS := (d.Yplus ⊔ d.S).subgroupOf I
  have hPYS : (P : Subgroup I) ≤ YS := by
    intro x hx
    exact mem_sup_right (hP ▸ mem_map_of_mem I.subtype hx)
  have hcore := pCoreIn_le_sylow YS (P.subtype hPYS)
  have hmap := map_mono (f := I.subtype) hcore
  rw [map_pCoreIn_of_injective 2 YS I.subtype I.subtype_injective,
    map_subgroupOf_eq_of_le (sup_le hYI hSI)] at hmap
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hPYS, hP] using hmap

/-- The lifted Borel places L intersect S in R = O₂(Y₊S). -/
theorem component_intersection_le_R [Finite G]
    (b : BorelIdentification d I c n F) (h : Earlier d I c) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S) : c.L ⊓ d.S ≤ d.R := by
  have hSI : d.S ≤ I := hP ▸ map_subtype_le (P : Subgroup I)
  apply le_pCoreIn_of_normalizes (d.T.isPGroup'.to_le (inf_le_right.trans inf_le_left))
    (inf_le_right.trans le_sup_right)
  apply sup_le (yplus_normalizes_intersection b h P hP)
  exact (le_inf (hSI.trans
    ((normal_subgroupOf_iff_le_normalizer (component_le c)).mp h.component_normal))
    d.S.le_normalizer).trans inf_normalizer_le_normalizer_inf

/-- B.6.1 for I and its actual Sylow S, lifted through the marked Borel. -/
theorem minimalParabolic_I [Finite G]
    (b : BorelIdentification d I c n F) (h : Earlier d I c)
    (hI : I ∈ d.HplusMinimal) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (hc : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I) :
    ChapterB.IsMinimalParabolicOver P ⊤ := by
  have hYM : d.Yplus ≤ d.M := (h.theta_eq ▸ theta_le (d.MI I)).trans inf_le_left
  have hgen := (lemma_15_3_27_4_of_containment d hI c P hP h.contains hYM).1
  exact minimalParabolic_supplement b h P hP hc le_rfl inf_le_right hgen P hP

/-- B.6.1 for LR and the Sylow subgroup whose ambient image is literally R. -/
theorem minimalParabolic_LR [Finite G]
    (b : BorelIdentification d I c n F) (h : Earlier d I c) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (hc : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    (Q : Sylow 2 ↥(c.L ⊔ d.R))
    (hQ : (Q : Subgroup ↥(c.L ⊔ d.R)).map (c.L ⊔ d.R).subtype = d.R) :
    ChapterB.IsMinimalParabolicOver Q ⊤ := by
  exact minimalParabolic_supplement b h P hP hc
    (R_le_S P hP (h.contains.trans (component_le c)))
    (component_intersection_le_R b h P hP) rfl Q hQ

/-- The complete local geometry needed before the pushing-up application. -/
theorem local_geometry [Finite G]
    (b : BorelIdentification d I c n F) (h : Earlier d I c)
    (hI : I ∈ d.HplusMinimal) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (hc : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I) :
    d.Yplus ≤ normalizer ((c.L ⊓ d.S : Subgroup G) : Set G) ∧
    ChapterB.IsMinimalParabolicOver P ⊤ ∧
    ∃ Q : Sylow 2 ↥(c.L ⊔ d.R),
      (Q : Subgroup ↥(c.L ⊔ d.R)).map (c.L ⊔ d.R).subtype = d.R ∧
      ChapterB.IsMinimalParabolicOver Q ⊤ := by
  obtain ⟨Q, hQ⟩ := exists_sylow_LR b h hI P hP
  exact ⟨yplus_normalizes_intersection b h P hP, minimalParabolic_I b h hI P hP hc,
    Q, hQ, minimalParabolic_LR b h P hP hc Q hQ⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp.Geometry

end
