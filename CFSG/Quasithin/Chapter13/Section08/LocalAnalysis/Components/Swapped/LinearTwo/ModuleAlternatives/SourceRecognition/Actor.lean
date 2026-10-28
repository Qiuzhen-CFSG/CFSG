module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.OriginalProjection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.Setup
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.SourceSections

/-!
# The literal exchanged field-four actor

The diagonal coset reduction of 13.8.16(1) forces the field degree to be two.
The two exchanged components then give product coordinates on their orbit
subgroup in H/O₂(H). The coordinates below retain both literal component
images, the Sylow image, and the actual element exchanging them. Thus the
abstract no-strong-module theorem applies to this source actor.

Source: Aschbacher–Smith, 13.8.16(1), printed pp.952–953.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
open F918Sections.NoStrong

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

open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H)
  (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K)
include d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving

theorem exists_source_exchangedActor {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (K : Set G)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (a : ExchangedActor KnownSimple.IsKnownSimple (Source.Hstar H) F 2),
      a.component = Source.starImage H K ∧
      a.second = Source.starImage H (K.conjBy t) ∧
      a.orbit = Source.starImage H (conjugateSpanBy K (T : Subgroup G)) ∧
      (a.sylow : Subgroup (Source.Hstar H)) = Source.starImage H T := by
  have hn2 := (Original.diagonal_cosets d h hF9all hcentral hcomm hsource
    hH hKH hK hgen hmoving hn hmodel ht htn).1
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  have hL := Original.one_le_orbit d h hF9all hcentral hcomm hsource
    hH hKH hK hmoving hn hmodel
  have hi := Original.moving_index d h hF9all hcentral hcomm hsource hH hKH hK hmoving
  have horbit := orbit_eq_two_conjugates H K T hKH hTH hi ht htn
  have hq := (SolvableSource.component_fitting_source d h hF9all hcentral hcomm hsource hH K hK).2
  obtain ⟨hBH,hB⟩ := conjugate_isCComponent H K hKH hK (hTH ht)
  let c := starConjugateEquiv H K hKH (hTH ht)
  let : IsQuasisimple (Source.starImage H K) := hq
  have hqB : IsQuasisimple (Source.starImage H (K.conjBy t)) := IsQuasisimple.of_mulEquiv c
  have hne : K ≠ K.conjBy t := fun he => htn (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  obtain ⟨e,he⟩ := exists_star_product_coordinates H K (K.conjBy t) hKH hBH hK hB hne hq hqB hmodel
  let N := Source.starImage H (conjugateSpanBy K (T : Subgroup G))
  let eN := e.trans (MulEquiv.subgroupCongr (congrArg (Source.starImage H) horbit.symm))
  have heN (a : Source.starImage H K) (b : Source.starImage H (K.conjBy t)) :
      (eN (a,b) : Source.Hstar H) = (a : Source.Hstar H) * b := he a b
  obtain ⟨F,hF,hfin,hcard,⟨f⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let S := (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hS : (S : Subgroup (Source.Hstar H)) = Source.starImage H T := by
    change ((T.subtype hTH : Sylow 2 H) : Subgroup H).map _ = _
    rw [Sylow.coe_subtype]
    rfl
  let ts := QuotientGroup.mk' (pCore 2 H) ⟨t,hTH ht⟩
  have hts : ts ∈ S := by
    change ts ∈ (S : Subgroup (Source.Hstar H))
    rw [hS]
    exact mem_map_of_mem _ ht
  have hAN : Source.starImage H K ≤ N := map_mono (subgroupOf_mono H (le_conjugateSpanBy K T))
  have hBN : Source.starImage H (K.conjBy t) ≤ N := by
    apply map_mono
    apply subgroupOf_mono H
    rw [horbit]
    exact le_sup_right
  refine ⟨F,hF,hfin,inferInstance,{
    degree_ge := le_rfl
    field_card := by simpa only [hn2] using hcard
    component := Source.starImage H K
    second := Source.starImage H (K.conjBy t)
    orbit := N
    sylow := S
    component_isComponent := F918Sections.star_isComponent H K hK hq
    second_isComponent := F918Sections.star_isComponent H _ hB hqB
    component_le := hAN
    second_le := hBN
    orbit_eq := by rw [hS]; exact F918Sections.star_conjugateSpan H K T hKH hTH
    orbit_normal := orbit_star_normal H K (one L T V₁) T hgen.symm hL
    generated := by rw [hS]; exact F918Sections.star_actor_generated H K _ T hgen.symm hL
    twoCore := pCore_quotient_pCore_eq_bot 2
    sqtk := by
      have hp : IsPGroup 2 V₁ := IsPGroup.of_card (n := 1) (by simpa using d.line_card)
      have hne : V₁ ≠ ⊥ := by
        intro heq
        have hc := d.line_card
        rw [heq,card_bot] at hc
        contradiction
      have hloc : IsTwoLocal (normalizer (V₁ : Set G)) := ⟨V₁,hne,hp,rfl⟩
      have hHN : H ≤ normalizer (V₁ : Set G) := d.first_normalizer ▸ hH.2.1
      have hsq := (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp
        ((d.counterexample.qtke.twoLocal_sqtk hloc).subgroup
          (H.subgroupOf (normalizer (V₁ : Set G))))
      exact ⟨LocalFitting.star_odd_rank d hH,hsq.isKGroup.quotient (pCore 2 H)⟩
    mover := ⟨ts,hts⟩
    moved := starImage_conjBy H K hKH (hTH ht)
    distinct := fun heq => starImages_ne H K _ hKH hBH hK hB hne heq.symm
    productEquiv := eN.symm.trans (MulEquiv.prodCongr f (c.symm.trans f))
    first_mark := first_mark _ _ _ eN heN f (c.symm.trans f)
    second_mark := second_mark _ _ _ eN heN f (c.symm.trans f) }, rfl, rfl, rfl, hS⟩

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
