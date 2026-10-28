module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition.NoStrong
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianExchangedFour


/-!
# The original exchanged field-four actor

Construct the exchanged actor on the literal H/O₂(H), retaining both
component images, their product coordinates, the image of the original
Sylow subgroup and its actual exchanging element. The original field-four
and Borel results supply the group hypotheses. The intrinsic no-strong-FF
theorem then applies to every faithful binary action of this same actor.
The full tensor/non-tensor filtration and source exclusion remain separate.

Source: Aschbacher–Smith 12.6.33, printed pp.837–838, using B.4.2 and F.9.18.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter13.Section08.Components Chapter13.Section08.Components.Swapped
open Chapter13.Section08.Components.Swapped.LinearTwo
open ModuleAlternatives.F918Sections ModuleAlternatives.F918Sections.NoStrong
open Chapter15.Section03.AbelianAmalgam.GenerationOne

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

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The exchanged model is marked by the actual original component, Sylow
image and conjugating element, through the full two-core quotient. -/
theorem SourceHypothesis.original_abelian_exchanged_actor
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    ∃ (t : G) (ht : t ∈ T) (hTH : (T : Subgroup G) ≤ H),
      t ∉ normalizer (K : Set G) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
        (a : ExchangedActor KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) F 2),
        a.component = actorImage H K ∧
        a.second = actorImage H (K.conjBy t) ∧
        a.orbit = actorImage H (conjugateSpanBy K (T : Subgroup G)) ∧
        (a.sylow : Subgroup (H ⧸ pCore 2 H)) = actorImage H T ∧
        (a.mover : H ⧸ pCore 2 H) = QuotientGroup.mk' (pCore 2 H) ⟨t,hTH ht⟩ := by
  obtain ⟨t,ht,hTH,htn,hOH,eb,P,heb,hP,hstar,hsol,hLB,hBM,hnB,heven,hrank,hOT,hBeq,hMeq⟩ :=
    S.original_abelian_exchanged_borel D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hgen hn (n := 2) (by decide) hm
  have hi : (normalizer (K.subgroupOf H : Set H)).index = 2 := by
    let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
    exact (cComponent_normalizer_index_quotient hK (pCore 2 H)).symm.trans
      (S.original_abelian_nonnormal_component_models D hZ z hz hTV hTz hbound hTI hns
        hH hKH hK hgen hn).1
  have horbit := orbit_eq_two_conjugates H K T hKH hTH hi ht htn
  have hq : IsQuasisimple (actorImage H K) :=
    (S.original_abelian_component_quasisimple D hZ z hz hTV hTz hbound hTI hns hH hKH hK).of_mulEquiv
      (componentStarEquiv H K hKH hK)
  have hmstar := hm.of_mulEquiv (componentStarEquiv H K hKH hK).symm
  obtain ⟨hBH,hB⟩ := conjugate_isCComponent H K hKH hK (hTH ht)
  let c := starConjugateEquiv H K hKH (hTH ht)
  let : IsQuasisimple (Chapter13.Section08.Source.starImage H K) := hq
  have hqB : IsQuasisimple (actorImage H (K.conjBy t)) := IsQuasisimple.of_mulEquiv c
  have hne : K ≠ K.conjBy t := fun he => htn (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  obtain ⟨e,he⟩ := exists_star_product_coordinates H K (K.conjBy t) hKH hBH hK hB hne hq hqB hmstar
  let N := actorImage H (conjugateSpanBy K (T : Subgroup G))
  let eN := e.trans (MulEquiv.subgroupCongr (congrArg (actorImage H) horbit.symm))
  have heN (a : actorImage H K) (b : actorImage H (K.conjBy t)) :
      (eN (a,b) : H ⧸ pCore 2 H) = (a : H ⧸ pCore 2 H) * b := he a b
  obtain ⟨F,hF,hfin,hcard,⟨f⟩⟩ := hmstar
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (f := 2)
    (by simpa [Nat.card_eq_fintype_card] using hcard)
  let Pstar := (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hS : (Pstar : Subgroup (H ⧸ pCore 2 H)) = actorImage H T := by
    change ((T.subtype hTH : Sylow 2 H) : Subgroup H).map _ = _
    rw [Sylow.coe_subtype]
    rfl
  let ts := QuotientGroup.mk' (pCore 2 H) ⟨t,hTH ht⟩
  have hts : ts ∈ Pstar := by
    change ts ∈ (Pstar : Subgroup (H ⧸ pCore 2 H))
    rw [hS]
    exact mem_map_of_mem _ ht
  have hAN : actorImage H K ≤ N := map_mono (subgroupOf_mono H (le_conjugateSpanBy K T))
  have hBN : actorImage H (K.conjBy t) ≤ N := by
    apply map_mono
    apply subgroupOf_mono H
    rw [horbit]
    exact le_sup_right
  have hres := S.original_abelian_exchanged_threeResidual D hZ z hz hTV hTz hbound hTI hns
    hH hKH hK hgen hn (n := 2) (by decide) hm
  have hN : N.Normal := by
    have hOn : ((conjugateSpanBy K (T : Subgroup G)).subgroupOf H).Normal := by
      rw [←hres]
      change (((primeToResidual 3 H).map H.subtype).comap H.subtype).Normal
      rw [comap_map_eq_self_of_injective H.subtype_injective]
      infer_instance
    exact hOn.map _ (QuotientGroup.mk'_surjective _)
  have hgenerated : N ⊔ (Pstar : Subgroup (H ⧸ pCore 2 H)) = ⊤ := by
    rw [hS]
    change ((conjugateSpanBy K (T : Subgroup G)).subgroupOf H).map _ ⊔
      ((T : Subgroup G).subgroupOf H).map _ = _
    rw [←Subgroup.map_sup,←subgroupOf_sup hOH hTH,hOT,subgroupOf_self]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  refine ⟨t,ht,hTH,htn,F,hF,hfin,inferInstance,{
    degree_ge := le_rfl
    field_card := hcard
    component := actorImage H K
    second := actorImage H (K.conjBy t)
    orbit := N
    sylow := Pstar
    component_isComponent := star_isComponent H K hK hq
    second_isComponent := star_isComponent H _ hB hqB
    component_le := hAN
    second_le := hBN
    orbit_eq := by rw [hS]; exact star_conjugateSpan H K T hKH hTH
    orbit_normal := hN
    generated := hgenerated
    twoCore := pCore_quotient_pCore_eq_bot 2
    sqtk := S.original_star_sqtk D hZ z hz hH
    mover := ⟨ts,hts⟩
    moved := starImage_conjBy H K hKH (hTH ht)
    distinct := fun heq => starImages_ne H K _ hKH hBH hK hB hne heq.symm
    productEquiv := eN.symm.trans (MulEquiv.prodCongr f (c.symm.trans f))
    first_mark := first_mark _ _ _ eN heN f (c.symm.trans f)
    second_mark := second_mark _ _ _ eN heN f (c.symm.trans f) },rfl,rfl,rfl,hS,rfl⟩

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- B.4.2 excludes strong FF modules on every faithful binary action of the
actual exchanged field-four quotient, with no classification callback. -/
theorem SourceHypothesis.original_abelian_exchanged_not_strong
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4)
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (ρ : Representation (ZMod 2) (H ⧸ pCore 2 H) U)
    (hf : Function.Injective ρ) : ¬ IsStrongFFModule ρ := by
  obtain ⟨t,ht,hTH,htn,F,hF,hfin,hchar,a,ha,hb,ho,hT,hts⟩ :=
    S.original_abelian_exchanged_actor D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hgen hn hm
  exact ModuleAlternatives.SourceRecognition.exchanged_not_strong a ρ hf
end CFSG.Quasithin.Chapter12.Section06

