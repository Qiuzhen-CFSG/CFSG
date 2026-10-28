module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NonnormalBinarySourceAt.Movement
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.SectionImages
public import Theory.Representation.BinaryOffender.SmallMovedProducts

/-!
# The actual exchanged field-four actor

The field-four comparison places the two original components in the full
point normalizer. Their literal quotient product, the ambient Sylow image,
and a moving Sylow element give an exchanged actor on H/O₂(H). The product
coordinates retain both component markings; no module recognition is
assumed. This supplies the actor used on the original U/V₁ section and its
proper quotients.

Source: Aschbacher–Smith, proof of 14.7.32, printed pp.1056–1057,
refs/quasithin.pdf.
-/

/-! This same-G,T source replay uses only Structural1222At and Theorem12213At
at the original Sylow; it does not infer universal earlier records. -/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.Components Swapped Swapped.LinearTwo
open ModuleAlternatives F918Sections.NoStrong
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem first_mark {D P : Type*} [Group D] [Group P]
    (A B N : Subgroup D) (e : A × B ≃* N)
    (he : ∀ a b, (e (a,b) : D) = (a : D) * b)
    (f : A ≃* P) (g : B ≃* P) :
    (A.subgroupOf N).map (e.symm.trans (MulEquiv.prodCongr f g)).toMonoidHom =
      (⊤ : Subgroup P).prod ⊥ := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    have hx' : e (⟨x,hx⟩,1) = x := Subtype.ext (by simpa using he ⟨x,hx⟩ 1)
    change True ∧ g (e.symm x).2 = 1
    rw [← hx', e.symm_apply_apply]
    exact ⟨trivial, g.map_one⟩
  · rintro ⟨_,hz⟩
    have hz' : z.2 = 1 := hz
    refine ⟨e (f.symm z.1,1),?_,?_⟩
    · change (e (f.symm z.1,1) : D) ∈ A
      rw [he,Subgroup.coe_one,mul_one]
      exact (f.symm z.1).property
    · change (f (e.symm (e (f.symm z.1,1))).1,
        g (e.symm (e (f.symm z.1,1))).2) = z
      simp only [e.symm_apply_apply,f.apply_symm_apply,map_one]
      exact Prod.ext rfl hz'.symm

private theorem second_mark {D P : Type*} [Group D] [Group P]
    (A B N : Subgroup D) (e : A × B ≃* N)
    (he : ∀ a b, (e (a,b) : D) = (a : D) * b)
    (f : A ≃* P) (g : B ≃* P) :
    (B.subgroupOf N).map (e.symm.trans (MulEquiv.prodCongr f g)).toMonoidHom =
      (⊥ : Subgroup P).prod ⊤ := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    have hx' : e (1,⟨x,hx⟩) = x := Subtype.ext (by simpa using he 1 ⟨x,hx⟩)
    change f (e.symm x).1 = 1 ∧ True
    rw [← hx',e.symm_apply_apply]
    exact ⟨f.map_one,trivial⟩
  · rintro ⟨hz,_⟩
    have hz' : z.1 = 1 := hz
    refine ⟨e (1,g.symm z.2),?_,?_⟩
    · change (e (1,g.symm z.2) : D) ∈ B
      rw [he,Subgroup.coe_one,one_mul]
      exact (g.symm z.2).property
    · change (f (e.symm (e (1,g.symm z.2))).1,
        g (e.symm (e (1,g.symm z.2))).2) = z
      simp only [e.symm_apply_apply,g.apply_symm_apply,map_one]
      exact Prod.ext hz'.symm rfl

theorem local_nonnormal_component_exchanged_actor_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    ∃ t : G, t ∈ T ∧ t ∉ normalizer (K : Set G) ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
        (a : ExchangedActor KnownSimple.IsKnownSimple (HStar F.H) k 2),
        a.component = Chapter13.Section08.Source.starImage F.H K ∧
        a.second = Chapter13.Section08.Source.starImage F.H (K.conjBy t) ∧
        a.orbit = Chapter13.Section08.Source.starImage F.H (conjugateSpanBy K (T : Subgroup G)) ∧
        (a.sylow : Subgroup (HStar F.H)) = Chapter13.Section08.Source.starImage F.H T := by
  obtain ⟨hfull,hres⟩ := local_nonnormal_component_full_component_at d h hab structural previous faithful earlier
    I K hI hKI hK hnormal
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  have hKH : K ≤ F.H := hKI.trans hI.2.1
  have hTH := F.sylow_le_of_mem_Hz hH
  have hnon : ¬ (K.subgroupOf F.H).Normal := by
    intro hn
    exact hnormal ((normal_subgroupOf_iff_le_normalizer hKI).mpr
      (hI.2.1.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn)))
  have hm := local_nonnormal_component_field_four_at d h hab structural previous faithful earlier
    F.H K hH hKH hfull hnon
  have hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K := by
    intro he
    exact hnon (normal_of_sylow_span_eq F.H K T hKH hTH
      ((Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
        (local_star_sqtk h F.H hH) hfull).imp_right And.left) he)
  obtain ⟨t,ht,htn⟩ := exists_moving_element K (T : Subgroup G) hmoving
  have hi := ((Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
    (local_star_sqtk h F.H hH) hfull).resolve_left hnon).1
  have horbit := orbit_eq_two_conjugates F.H K T hKH hTH hi ht htn
  have hq := (WholeResidualAssembly.GuardedSource.local_component_star_isComponent h hab structural previous faithful F.H hH _ hfull).2
  obtain ⟨hBH,hB⟩ := conjugate_isCComponent F.H K hKH hfull (hTH ht)
  let c := starConjugateEquiv F.H K hKH (hTH ht)
  let : IsQuasisimple (Chapter13.Section08.Source.starImage F.H K) := hq
  have hqB : IsQuasisimple (Chapter13.Section08.Source.starImage F.H (K.conjBy t)) :=
    IsQuasisimple.of_mulEquiv c
  have hne : K ≠ K.conjBy t := fun he => htn (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  obtain ⟨e,he⟩ := exists_star_product_coordinates F.H K (K.conjBy t) hKH hBH
    hfull hB hne hq hqB hm
  let N := Chapter13.Section08.Source.starImage F.H (conjugateSpanBy K (T : Subgroup G))
  let eN := e.trans (MulEquiv.subgroupCongr
    (congrArg (Chapter13.Section08.Source.starImage F.H) horbit.symm))
  have heN (a : Chapter13.Section08.Source.starImage F.H K)
      (b : Chapter13.Section08.Source.starImage F.H (K.conjBy t)) :
      (eN (a,b) : HStar F.H) = (a : HStar F.H) * b := he a b
  obtain ⟨k,hk,hfin,hcard,⟨f⟩⟩ := hm
  let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
    (show Nat.card k = 2^2 by simpa using hcard)
  let S := (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 F.H))
  have hS : (S : Subgroup (HStar F.H)) = Chapter13.Section08.Source.starImage F.H T := by
    change ((T.subtype hTH : Sylow 2 F.H) : Subgroup F.H).map _ = _
    rw [Sylow.coe_subtype]
    rfl
  let ts := QuotientGroup.mk' (pCore 2 F.H) ⟨t,hTH ht⟩
  have hts : ts ∈ S := by
    change ts ∈ (S : Subgroup (HStar F.H))
    rw [hS]
    exact mem_map_of_mem _ ht
  have hAN : Chapter13.Section08.Source.starImage F.H K ≤ N :=
    map_mono (subgroupOf_mono F.H (le_conjugateSpanBy K T))
  have hBN : Chapter13.Section08.Source.starImage F.H (K.conjBy t) ≤ N := by
    apply map_mono
    apply subgroupOf_mono F.H
    rw [horbit]
    exact le_sup_right
  have hg := (local_nonnormal_component_eq_full_point_at d h hab structural previous faithful earlier
    I K hI hKI hK hnormal).1
  have hNT : conjugateSpanBy K (T : Subgroup G) ≤ F.H := hg ▸ le_sup_left
  have hNn : (conjugateSpanBy K (T : Subgroup G)).subgroupOf F.H |>.Normal :=
    (normal_subgroupOf_iff_le_normalizer hNT).mpr (by
      rw [hg]
      exact sup_le (conjugateSpanBy K (T : Subgroup G)).le_normalizer
        (le_normalizer_conjugateSpanBy K (T : Subgroup G)))
  refine ⟨t,ht,htn,k,hk,hfin,inferInstance,{
    degree_ge := le_rfl
    field_card := by simpa using hcard
    component := Chapter13.Section08.Source.starImage F.H K
    second := Chapter13.Section08.Source.starImage F.H (K.conjBy t)
    orbit := N
    sylow := S
    component_isComponent := F918Sections.star_isComponent F.H K hfull hq
    second_isComponent := F918Sections.star_isComponent F.H _ hB hqB
    component_le := hAN
    second_le := hBN
    orbit_eq := by rw [hS]; exact F918Sections.star_conjugateSpan F.H K T hKH hTH
    orbit_normal := hNn.map _ (QuotientGroup.mk'_surjective _)
    generated := by
      rw [hS]
      change ((conjugateSpanBy K (T : Subgroup G)).subgroupOf F.H).map _ ⊔
        ((T : Subgroup G).subgroupOf F.H).map _ = ⊤
      rw [←Subgroup.map_sup,←subgroupOf_sup hNT hTH,←hg,subgroupOf_self,
        map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    twoCore := pCore_quotient_pCore_eq_bot 2
    sqtk := local_star_sqtk h F.H hH
    mover := ⟨ts,hts⟩
    moved := starImage_conjBy F.H K hKH (hTH ht)
    distinct := fun heq => starImages_ne F.H K _ hKH hBH hfull hB hne heq.symm
    productEquiv := eN.symm.trans (MulEquiv.prodCongr f (c.symm.trans f))
    first_mark := first_mark _ _ _ eN heN f (c.symm.trans f)
    second_mark := second_mark _ _ _ eN heN f (c.symm.trans f) }, rfl, rfl, rfl, hS⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
