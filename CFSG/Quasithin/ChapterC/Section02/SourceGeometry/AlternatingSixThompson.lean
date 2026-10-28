module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Syntheme
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.OriginalGeometry
public import CFSG.Quasithin.ChapterC.Section02.RankOneOffenders
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.DualExtensions.Reduction

/-!
# The syntheme parabolic in the actual natural A6 row

The ratio-one moved section puts every best offender in the component.
Their unique syntheme four-group images generate the actual Thompson image.
C.2.3 normalizer control therefore places its syntheme stabilizer inside
the proper marked intersection; maximality gives equality. The original
relative input and literal star quotient are retained throughout.

Source: Aschbacher--Smith B.5.1, C.2.7(3) and 15.3.21,
printed pp.99--103,146--147,1127.
-/
set_option backward.isDefEq.respectTransparency false
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

theorem ratio_one_component_eq_offender
    (h : Input κ H R M K)
    (hCJ : starImage K R K ≤ offenderSubgroup (starRepresentation K R))
    (s : MovedSection ((starRepresentation K R).comp (offenderSubgroup (starRepresentation K R)).subtype)
      ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))))
    (hgen : offenderSubgroup s.action =
      (starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R)))
    (hratio : quadraticRatio s.action = 1) :
    offenderSubgroup (starRepresentation K R) = starImage K R K := by
  let D := K ⊔ R
  let C := starImage K R K
  let J := offenderSubgroup (starRepresentation K R)
  let : (K.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le K.le_normalizer h.normalizes)
  let : C.Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  let : (C.subgroupOf J).Normal := inferInstanceAs (C.comap J.subtype).Normal
  have hh := ExtensionConsequences.DualExtensions.section_generated s hratio
    (offenderSubgroup_restrict_eq_top (starRepresentation K R))
  rw [hgen] at hh
  exact le_antisymm (subgroupOf_eq_top.mp hh) hCJ

theorem alternatingSix_bestOffender_family
    (h : Input κ H R M K)
    (hCJ : starImage K R K ≤ offenderSubgroup (starRepresentation K R))
    (s : MovedSection ((starRepresentation K R).comp (offenderSubgroup (starRepresentation K R)).subtype)
      ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))))
    (hgen : offenderSubgroup s.action =
      (starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R)))
    (e : ActionEquiv (s.action.comp
      ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))).subtype)
      (alternatingNatural 6))
    (hoff : ∀ A, IsBestOffender s.action A → rank A = 2 ∧
      ∃ g : alternatingGroup (Fin 6),
        ((A.subgroupOf ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R)))).map
          ((alternatingGroup (Fin 6)).subtype.comp e.groupEquiv.toMonoidHom)) =
          (ChapterB.Offenders.evenPart 6).map (MulAut.conj (g : Equiv.Perm (Fin 6))).toMonoidHom)
    (hratio : quadraticRatio s.action = 1) :
    let C := starImage K R K
    let eC := (subgroupOfEquivOfLe hCJ).symm.trans e.groupEquiv
    ∀ A, IsBestOffender (starRepresentation K R) A →
      A ≤ C ∧ ChapterB.Offenders.IsConjugateTo
        ((A.subgroupOf C).map ((alternatingGroup (Fin 6)).subtype.comp eC.toMonoidHom))
        (ChapterB.Offenders.evenPart 6) := by
  intro C eC A hA
  have hJ := ratio_one_component_eq_offender h hCJ s hgen hratio
  have hAJ := hA.le_offenderSubgroup (starRepresentation K R)
  refine ⟨hAJ.trans hJ.le,?_⟩
  have hA' := hA.subgroupOf (starRepresentation K R) hAJ
  have hAm := IrreducibleBranch.moved_offender s (hA'.isOffender _)
  obtain ⟨_,g,hg⟩ := hoff _ (hAm.best_and_codim_eq_of_quadraticRatio_eq_one _ hratio).1
  refine ⟨g,?_⟩
  rw [←hg]
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨(subgroupOfEquivOfLe hCJ).symm a,ha,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨subgroupOfEquivOfLe hCJ a,ha,rfl⟩

section
variable {D E : Type*} [Group D] [Finite D] [Group E] [Finite E]

theorem thompson_image_evenPart_of_bestOffenders
    (V R : Subgroup D) [V.Normal] [IsElementaryAbelian 2 V]
    (hR : IsPGroup 2 R) (hVR : V ≤ R)
    (q : D →* E) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set D))
    (hnoncentral : ¬ elementaryAbelianMaxJ R ≤ q.ker)
    (C : Subgroup E) (e : C ≃* alternatingGroup (Fin 6))
    (hoff : ∀ A, IsBestOffender (NormalElementaryQuotient.representation V q hq hker) A →
      A ≤ C ∧ ChapterB.Offenders.IsConjugateTo
        ((A.subgroupOf C).map ((alternatingGroup (Fin 6)).subtype.comp e.toMonoidHom))
        (ChapterB.Offenders.evenPart 6)) :
    (elementaryAbelianMaxJ R).map q ≤ C ∧
      ChapterB.Offenders.IsConjugateTo
        (((elementaryAbelianMaxJ R).map q).subgroupOf C |>.map
          ((alternatingGroup (Fin 6)).subtype.comp e.toMonoidHom))
        (ChapterB.Offenders.evenPart 6) := by
  let f := (alternatingGroup (Fin 6)).subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hmax := (ChapterB.lemma_B_2_7_local V q hq hker R hVR hnoncentral).2
  have hmem (A : Subgroup D) (hA : A ∈ elementaryAbelianMaxSubgroups R)
      (hne : A.map q ≠ ⊥) := hmax _ ⟨A,hA,rfl,hne⟩
  have hex : ∃ A ∈ elementaryAbelianMaxSubgroups R, A.map q ≠ ⊥ := by
    by_contra! hall
    apply hnoncentral
    exact sSup_le fun A hA => (map_eq_bot_iff A).mp (hall A hA)
  obtain ⟨A,hA,hAne⟩ := hex
  obtain ⟨hAC,hAf⟩ := hoff _ (hmem A hA hAne)
  have hfamily (B : Subgroup D) (hB : B ∈ elementaryAbelianMaxSubgroups R)
      (hne : B.map q ≠ ⊥) : B.map q = A.map q := by
    obtain ⟨hBC,hBf⟩ := hoff _ (hmem B hB hne)
    have heq := ChapterB.Offenders.Six.evenPart_conjugates_eq_in_twoGroup
      (((R.map q).subgroupOf C).map f) (((hR.map q).comap_subtype).map f)
      hBf hAf (map_mono (comap_mono (map_mono hB.1)))
      (map_mono (comap_mono (map_mono hA.1)))
    have heq' := map_injective hf heq
    have hm := congrArg (map C.subtype) heq'
    simpa only [map_subgroupOf_eq_of_le hAC,map_subgroupOf_eq_of_le hBC] using hm
  have heq : (elementaryAbelianMaxJ R).map q = A.map q := by
    apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      apply sSup_le
      intro B hB
      apply map_le_iff_le_comap.mp
      by_cases hz : B.map q = ⊥
      · rw [hz]; exact bot_le
      · exact (hfamily B hB hz).le
    · exact map_mono (le_sSup hA)
  exact ⟨heq ▸ hAC,heq ▸ hAf⟩
end
theorem alternatingSix_thompson_from_source
    (h : Input κ H R M K)
    (hCJ : starImage K R K ≤ offenderSubgroup (starRepresentation K R))
    (s : MovedSection ((starRepresentation K R).comp (offenderSubgroup (starRepresentation K R)).subtype)
      ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))))
    (hgen : offenderSubgroup s.action =
      (starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R)))
    (e : ActionEquiv (s.action.comp
      ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))).subtype)
      (alternatingNatural 6))
    (hoff : ∀ A, IsBestOffender s.action A → rank A = 2 ∧
      ∃ g : alternatingGroup (Fin 6),
        ((A.subgroupOf ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R)))).map
          ((alternatingGroup (Fin 6)).subtype.comp e.groupEquiv.toMonoidHom)) =
          (ChapterB.Offenders.evenPart 6).map (MulAut.conj (g : Equiv.Perm (Fin 6))).toMonoidHom)
    (hratio : quadraticRatio s.action = 1) :
    let C := starImage K R K
    let eC := (subgroupOfEquivOfLe hCJ).symm.trans e.groupEquiv
    starImage K R (elementaryAbelianMaxJ R) ≤ C ∧
      ChapterB.Offenders.IsConjugateTo
        (((starImage K R (elementaryAbelianMaxJ R)).subgroupOf C).map
          ((alternatingGroup (Fin 6)).subtype.comp eC.toMonoidHom))
        (ChapterB.Offenders.evenPart 6) := by
  intro C eC
  let D := K ⊔ R
  let R₀ := R.subgroupOf D
  let q := QuotientGroup.mk' (starKernel K R)
  let : (K.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le K.le_normalizer h.normalizes)
  have hj := source_join_input h
  have hR : IsPGroup 2 R := by
    have hh := h.setup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le h.setup.radical_le] at hh
  have hQR : pCore 2 D ≤ R₀ := fun x hx => source_joinCore_le_radical hj
    (mem_map_of_mem D.subtype hx)
  have hVR : starV K R ≤ R₀ := (map_subtype_le _).trans hQR
  have hn : ¬elementaryAbelianMaxJ R₀ ≤ q.ker := by
    simpa only [q,QuotientGroup.ker_mk'] using thompson_not_le_starKernel_of_normal_input hj
  have hh := thompson_image_evenPart_of_bestOffenders (starV K R) R₀ hR.comap_subtype hVR q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hn C eC
    (alternatingSix_bestOffender_family h hCJ s hgen e hoff hratio)
  have hJR : elementaryAbelianMaxJ R ≤ D :=
    (sSup_le fun _ hA => hA.1).trans (show R ≤ D from le_sup_right)
  have hJ : elementaryAbelianMaxJ R₀ = (elementaryAbelianMaxJ R).subgroupOf D := by
    apply map_injective D.subtype_injective
    rw [←elementaryAbelianMaxJ_map_injective D.subtype D.subtype_injective,
      map_subgroupOf_eq_of_le (show R ≤ D from le_sup_right),map_subgroupOf_eq_of_le hJR]
  simpa only [hJ,starImage,q,D] using hh

end CFSG.Quasithin.ChapterC.C27Source

public section
open Subgroup Theory.SpecificGroups.SymmetricSix
namespace CFSG.Quasithin.ChapterC.C27Source
variable {D : Type*} [Group D]

theorem alternatingSix_parabolic_of_thompson
    (e : D ≃* alternatingGroup (Fin 6)) (T P : Subgroup D)
    (hP : P ≠ ⊤) (hn : normalizer (T : Set D) ≤ P)
    (ht : ChapterB.Offenders.IsConjugateTo
      (T.map ((alternatingGroup (Fin 6)).subtype.comp e.toMonoidHom))
      (ChapterB.Offenders.evenPart 6)) :
    ∃ g : Equiv.Perm (Fin 6), P.map e.toMonoidHom =
      a6SynthemeStabilizer.map (MulAut.conjNormal g).toMonoidHom := by
  obtain ⟨g,hg⟩ := ht
  let a : MulAut (alternatingGroup (Fin 6)) := MulAut.conjNormal g
  have ht' : T.map e.toMonoidHom =
      ((ChapterB.Offenders.evenPart 6).subgroupOf (alternatingGroup (Fin 6))).map a.toMonoidHom := by
    apply map_injective (alternatingGroup (Fin 6)).subtype_injective
    rw [map_map,hg,map_map]
    change _ = ((ChapterB.Offenders.evenPart 6).subgroupOf (alternatingGroup (Fin 6))).map
      ((MulAut.conj g).toMonoidHom.comp (alternatingGroup (Fin 6)).subtype)
    rw [←map_map,map_subgroupOf_eq_of_le (show ChapterB.Offenders.evenPart 6 ≤ alternatingGroup (Fin 6) from inf_le_right)]
  have hle : a6SynthemeStabilizer.map a.toMonoidHom ≤ P.map e.toMonoidHom := by
    calc
      _ ≤ (normalizer ((ChapterB.Offenders.evenPart 6).subgroupOf
          (alternatingGroup (Fin 6)) : Set (alternatingGroup (Fin 6)))).map a.toMonoidHom :=
        map_mono ChapterB.Offenders.Six.syntheme_le_normalizer_evenPart
      _ = normalizer (T.map e.toMonoidHom : Set (alternatingGroup (Fin 6))) := by
        rw [map_normalizer_eq_of_bijective (f := a.toMonoidHom) _ a.bijective,ht']
      _ = (normalizer (T : Set D)).map e.toMonoidHom :=
        (map_normalizer_eq_of_bijective _ e.bijective).symm
      _ ≤ _ := map_mono hn
  have hp : P.map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply hP
    have hh := congrArg (comap e.toMonoidHom) he
    simpa only [comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective,comap_top] using hh
  have hc : IsCoatom (a6SynthemeStabilizer.map a.toMonoidHom) :=
    (a.mapSubgroup.isCoatom_iff a6SynthemeStabilizer).mpr a6SynthemeStabilizer_isCoatom
  refine ⟨g,?_⟩
  by_contra he
  exact hp (hc.2 _ (lt_of_le_of_ne hle (Ne.symm he)))
end CFSG.Quasithin.ChapterC.C27Source

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

theorem alternatingSix_marked_parabolic_from_source
    (h : Input κ H R M K)
    (hCJ : starImage K R K ≤ offenderSubgroup (starRepresentation K R))
    (s : MovedSection ((starRepresentation K R).comp (offenderSubgroup (starRepresentation K R)).subtype)
      ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))))
    (hgen : offenderSubgroup s.action =
      (starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R)))
    (e : ActionEquiv (s.action.comp
      ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))).subtype)
      (alternatingNatural 6))
    (hoff : ∀ A, IsBestOffender s.action A → rank A = 2 ∧
      ∃ g : alternatingGroup (Fin 6),
        ((A.subgroupOf ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R)))).map
          ((alternatingGroup (Fin 6)).subtype.comp e.groupEquiv.toMonoidHom)) =
          (ChapterB.Offenders.evenPart 6).map (MulAut.conj (g : Equiv.Perm (Fin 6))).toMonoidHom)
    (hratio : quadraticRatio s.action = 1) :
    let C := starImage K R K
    let eC := (subgroupOfEquivOfLe hCJ).symm.trans e.groupEquiv
    ∃ g : Equiv.Perm (Fin 6),
      ((starM K R M).subgroupOf C).map eC.toMonoidHom =
        Theory.SpecificGroups.SymmetricSix.a6SynthemeStabilizer.map
          (MulAut.conjNormal g).toMonoidHom := by
  intro C eC
  let T := starImage K R (elementaryAbelianMaxJ R)
  let P := (starM K R M).subgroupOf C
  obtain ⟨htC,ht⟩ := alternatingSix_thompson_from_source h hCJ s hgen e hoff hratio
  have hm := star_thompson_intersection_from_source h
  have hp : P ≠ ⊤ := fun he => hm.2.not_ge (subgroupOf_eq_top.mp he)
  have hn : normalizer (T.subgroupOf C : Set C) ≤ P := by
    intro x hx
    have hxN : (x : StarQuotient K R) ∈ normalizer (T : Set (StarQuotient K R)) := by
      rw [←map_subgroupOf_eq_of_le (show T ≤ C from htC)]
      exact (T.subgroupOf C).le_normalizer_map C.subtype ⟨x,hx,rfl⟩
    exact hm.1 ⟨x.property,hxN⟩
  exact alternatingSix_parabolic_of_thompson eC (T.subgroupOf C) P hp hn ht

end CFSG.Quasithin.ChapterC.C27Source
