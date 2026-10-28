module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversalIndices
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.Actors
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.CoverAlgebra
public import Theory.GroupTheory.NormalGenerationFixedQuotient
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.ComponentCommutator
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups.Coordinates

/-!
# Excluding the saturated marked tensor critical pair

Suppose the actual star images of Uγ and Vγ coincide and their common
H-conjugate is the point radical of SL₃(2) × S₃. A natural tensor chief
section has fixed codimension four for this radical. The critical index
comparison and the line-valued D_H commutator give the upper bound

  4 ≤ codim C(Uγ*) ≤ codim D̃_H + 2 dim Ã₁ ≤ 2 + 2.

Consequently codim D̃_H = 2 and A₁ ≤ U_H. Conjugation by the inverse
critical conjugator puts the reverse V-group inside O₂(L₁T). The genuine
D_H/Dγ transport makes its U-group have star rank two, so both reverse
star images fill that same order-four radical. Since the reverse U-group
contains V₁, equality of its star image with the reverse V-group forces
[U_H, V_H^(g⁻¹)] ≤ U_H^(g⁻¹). Transporting back gives
[U_H^g, V_H] ≤ U_H, contrary to the noncentral normally generated section
V_H/U_H and the generation conclusion of 13.8.18(1).

Only the literal chief section is identified with the tensor module. Its
faithfulness implies faithfulness of U_H/V₁; there is no faithfulness
transfer to V_H/U_H and no assertion that quadratic point radicals have
rank one. Normality is always relative to the displayed local group.

The exported theorem is the saturated-branch contradiction, with the actual
source action, marked product, seed and critical conjugators retained.
The compatible marking, chief section, and the two concrete tensor facts
remain explicit inputs for the parent assembly. This does not prove the
proper-subgroup branch or the whole of 13.8.21(1).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.21(1), printed p.957, using 13.8.4(5), 13.8.18(1), F.9.13(2,6)
and the critical index comparison in 13.8.8 / F.9.16. The argument uses the
actual inverse conjugator, without assuming the original pair is symmetric.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter13.Section08
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve
open FieldComponents.LinearThree FieldComponents.LinearThree.ExternalModules
open FieldComponents.LinearThree.ExternalModules.MarkedCritical
open AlternatingAndLinear.FourStructure.CriticalTransfer
open AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical.SaturatedPair

-- Evaluate displacement at two generators; its kernel is the fixed space.
private theorem two_generator_bound {J W : Type*} [Group J]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) J W) (A : Subgroup J)
    (a b : J) (ha : a ∈ A) (hb : b ∈ A)
    (hgen : ∀ x ∈ A, x = 1 ∨ x = a ∨ x = b ∨ x = a * b)
    (D S : Submodule (ZMod 2) W)
    (hcomm : ∀ x ∈ A, ∀ d ∈ D, ρ x d - d ∈ S) :
    fixedCodim ρ A ≤ Module.finrank (ZMod 2) (W ⧸ D) +
      2 * Module.finrank (ZMod 2) S := by
  let f : D →ₗ[ZMod 2] S × S :=
    (((ρ a - LinearMap.id).comp D.subtype).codRestrict S (fun d => hcomm a ha d d.property)).prod
      (((ρ b - LinearMap.id).comp D.subtype).codRestrict S (fun d => hcomm b hb d d.property))
  have hk : (LinearMap.ker f).map D.subtype ≤ fixedSpace ρ A := by
    rintro _ ⟨d, hd, rfl⟩ x
    have ha' : ρ a d = d := sub_eq_zero.mp (congrArg (fun v : S × S => (v.1 : W)) hd)
    have hb' : ρ b d = d := sub_eq_zero.mp (congrArg (fun v : S × S => (v.2 : W)) hd)
    rcases hgen x x.property with he | he | he | he
    · change ρ x.val d = d; rw [he, map_one]; rfl
    · change ρ x.val d = d; rwa [he]
    · change ρ x.val d = d; rwa [he]
    · change ρ x.val d = d; rw [he, map_mul, Module.End.mul_apply, hb', ha']
  have hkdim := (Submodule.equivMapOfInjective D.subtype D.subtype_injective
    (LinearMap.ker f)).finrank_eq
  have hm := Submodule.finrank_mono hk
  have hn := f.finrank_range_add_finrank_ker
  have hd := D.finrank_quotient_add_finrank
  have hc := fixedCodim_add_finrank ρ A
  have hr := Submodule.finrank_le (LinearMap.range f)
  rw [Module.finrank_prod] at hr
  omega

private theorem radical_two_generators {J : Type*} [Group J]
    (e : J ≃* TensorGroup) (A : Subgroup J)
    (hA : A.map e.toMonoidHom = tensorPointRadical) :
    ∃ a ∈ A, ∃ b ∈ A, ∀ x ∈ A, x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  let f := componentInclusion.comp pointShear
  let a := e.symm (f (Multiplicative.ofAdd (1,0)))
  let b := e.symm (f (Multiplicative.ofAdd (0,1)))
  have hf (c : Multiplicative (ZMod 2 × ZMod 2)) : e.symm (f c) ∈ A := by
    have hm : f c ∈ A.map e.toMonoidHom := by
      rw [hA]
      exact ⟨pointShear c, ⟨c,rfl⟩,rfl⟩
    obtain ⟨x,hx,he⟩ := hm
    have he' : e.symm (f c) = x := by rw [← he]; exact e.symm_apply_apply x
    exact he'.symm ▸ hx
  refine ⟨a, hf _, b, hf _, ?_⟩
  intro x hx
  have hm : e x ∈ tensorPointRadical := hA ▸ mem_map_of_mem e.toMonoidHom hx
  obtain ⟨_, ⟨c,rfl⟩,he⟩ := hm
  have he' : x = e.symm (f c) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact he.symm
  have hc : c = 1 ∨ c = Multiplicative.ofAdd (1,0) ∨
      c = Multiplicative.ofAdd (0,1) ∨
      c = Multiplicative.ofAdd (1,0) * Multiplicative.ofAdd (0,1) := by
    rcases c with ⟨c,d⟩
    fin_cases c <;> fin_cases d
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr rfl))
  rcases hc with rfl | rfl | rfl | rfl
  · left; simpa only [map_one] using he'
  · right; left; exact he'
  · right; right; left; exact he'
  · right; right; right
    exact he'.trans ((congrArg e.symm (f.map_mul _ _)).trans (e.symm.map_mul _ _))

variable {G : Type*} [Group G]
variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

private def sourceSection (act : SourceAction H V₃ V₁)
    (hcentral : H ≤ centralizer (V₁ : Set G)) :
    ConjugationSection H (Source.UH H V₃) V₁ act.representation where
  le := conjugateSpanBy_le_self act.seed_le
  normalizes := le_normalizer_conjugateSpanBy V₃ H
  centralizes := hcentral
  line_le := act.line_le
  quotient := quotientMap H V₃ V₁
  surjective := QuotientGroup.mk'_surjective _
  kernel := QuotientGroup.ker_mk' _
  conjugates := act.conjugation

private theorem normalClosure_map (F H : Subgroup G) (hFH : F ≤ H) :
    (normalClosure (F.subgroupOf H : Set H)).map H.subtype = conjugateSpanBy F H := by
  have hSH := conjugateSpanBy_le_self hFH
  let : ((conjugateSpanBy F H).subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hSH).mpr (le_normalizer_conjugateSpanBy F H)
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    change normalClosure (F.subgroupOf H : Set H) ≤ (conjugateSpanBy F H).subgroupOf H
    exact normalClosure_le_normal (fun x hx => le_conjugateSpanBy F H hx)
  · apply (closure_le _).mpr
    rintro _ ⟨h,hh,f,hf,rfl⟩
    refine ⟨⟨h,hh⟩ * ⟨f,hFH hf⟩ * ⟨h,hh⟩⁻¹, ?_, rfl⟩
    exact (inferInstance : (normalClosure (F.subgroupOf H : Set H)).Normal).conj_mem
      ⟨f,hFH hf⟩ (le_normalClosure hf) ⟨h,hh⟩

private theorem source_noncentral (H P V V₃ F : Subgroup G)
    (hVH : V ≤ H) (hV₃V : V₃ ≤ V) (hPH : P ≤ H) (hFH : F ≤ H)
    (hgen : H = conjugateSpanBy F H ⊔ P)
    (hseed : ⁅P,V⁆ ≤ Source.UH H V₃)
    (hnoncentral : ¬ ⁅Source.VH H V,H⁆ ≤ Source.UH H V₃) :
    ¬ ⁅F,Source.VH H V⁆ ≤ Source.UH H V₃ := by
  intro hc
  have hUH : Source.UH H V₃ ≤ H := conjugateSpanBy_le_self (hV₃V.trans hVH)
  have hWH : Source.VH H V ≤ H := conjugateSpanBy_le_self hVH
  let : ((Source.UH H V₃).subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hUH).mpr (le_normalizer_conjugateSpanBy V₃ H)
  have hv : (Source.VH H V).subgroupOf H = normalClosure (V.subgroupOf H : Set H) := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hWH, normalClosure_map V H hVH]
    rfl
  have hg : normalClosure (F.subgroupOf H : Set H) ⊔ P.subgroupOf H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, normalClosure_map F H hFH, map_subgroupOf_eq_of_le hPH,
      ← MonoidHom.range_eq_map, range_subtype, ← hgen]
  have hfc : ⁅F.subgroupOf H,(Source.VH H V).subgroupOf H⁆ ≤
      (Source.UH H V₃).subgroupOf H := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rwa [map_commutator, map_subgroupOf_eq_of_le hFH,
      map_subgroupOf_eq_of_le hWH, map_subgroupOf_eq_of_le hUH]
  have hpc : ⁅P.subgroupOf H,V.subgroupOf H⁆ ≤ (Source.UH H V₃).subgroupOf H := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rwa [map_commutator, map_subgroupOf_eq_of_le hPH,
      map_subgroupOf_eq_of_le hVH, map_subgroupOf_eq_of_le hUH]
  have hh := map_mono (f := H.subtype) (commutator_le_of_normal_generation
    (F.subgroupOf H) (P.subgroupOf H) (V.subgroupOf H)
    ((Source.VH H V).subgroupOf H) ((Source.UH H V₃).subgroupOf H) hv hg hfc hpc)
  rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype, map_subgroupOf_eq_of_le hWH,
    map_subgroupOf_eq_of_le hUH, commutator_comm] at hh
  exact hnoncentral hh

private theorem equal_star_commutator {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {H U Z : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) W}
    (s : ConjugationSection H U Z ρ) (A B : Subgroup G)
    (hAB : A ≤ B) (hBH : B ≤ H) (hBA : B ≤ normalizer (A : Set G))
    (hUA : U ≤ normalizer (A : Set G)) (hZA : Z ≤ A)
    (he : Source.starImage H A = Source.starImage H B) : ⁅U,B⁆ ≤ A := by
  have hQ : ⁅Source.QH H,U⁆ ≤ Z := by
    apply commutator_le.mpr
    rintro x ⟨a,ha,rfl⟩ u hu
    apply (s.quotient_eq_zero_iff ⟨⁅(a:G),u⁆,s.commutator_mem a ⟨u,hu⟩⟩).mp
    have hq : QuotientGroup.mk' (pCore 2 H) a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
    rw [← s.displacement a ⟨u,hu⟩, hq, map_one]
    exact sub_self _
  have hfactor := CriticalGeometry.AsymmetricPair.eq_sup_inf_QH_of_starImage_eq H A B hAB hBH he
  have hh : B ≤ commutatorPreimage B U A := by
    rw [hfactor]
    apply sup_le
    · apply le_commutatorPreimage le_sup_left
      exact le_normalizer_iff_commutator_le_left.mp hUA
    · exact le_commutatorPreimage le_sup_right
        ((commutator_mono inf_le_right le_rfl).trans (hQ.trans hZA))
  rw [commutator_comm]
  exact (commutator_mono hh le_rfl).trans
    (commutator_commutatorPreimage_le B U A hBA)

-- Equality in the critical estimate supplies the line containment needed
-- on reversal. The reverse pair fills the parabolic core by cardinality.
private theorem saturated_core [Finite G]
    [FiniteDimensional (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]
    (act : SourceAction H V₃ V₁) (hcentral : H ≤ centralizer (V₁ : Set G))
    (V P : Subgroup G) (g : G) (h : H)
    (hVH : V ≤ H) (hflag : V₃ ≤ V) (hPH : P ≤ H)
    (hforward : (Source.VH H V).map (MulAut.conj g).toMonoidHom ≤ H)
    (hback : Source.VH H V ≤ (P.pCoreIn 2).map (MulAut.conj g).toMonoidHom)
    (hcard : Nat.card V₁ = 2)
    (hgen : H = conjugateSpanBy ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom) H ⊔ P)
    (hseed : ⁅P,V⁆ ≤ Source.UH H V₃)
    (hnoncentral : ¬ ⁅Source.VH H V,H⁆ ≤ Source.UH H V₃)
    (hfaith : Function.Injective act.representation)
    (eH : Source.Hstar H ≃* TensorGroup)
    (hmark : (Source.starImage H (((Source.VH H V).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj (h:G)).toMonoidHom)).map eH.toMonoidHom = tensorPointRadical)
    (hsat : Source.starImage H ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom) =
      Source.starImage H ((Source.VH H V).map (MulAut.conj g).toMonoidHom))
    (hparabolic : (Source.starImage H (P.pCoreIn 2)).map eH.toMonoidHom = tensorPointRadical)
    (hcritical : Nat.log 2 ((Source.DH (Source.UH H V₃)
        ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)
        (V₁.map (MulAut.conj g).toMonoidHom)).relIndex (Source.UH H V₃)) ≤
      Nat.log 2 ((Source.Dgamma ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)
        (Source.UH H V₃) V₁).relIndex ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)))
    (hlower : 4 ≤ fixedCodim act.representation
      (Source.starImage H ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom))) : False := by
  let s := sourceSection H V₃ V₁ act hcentral
  let U := Source.UH H V₃
  let Ug := U.map (MulAut.conj g).toMonoidHom
  let Vg := (Source.VH H V).map (MulAut.conj g).toMonoidHom
  let A₁ := V₁.map (MulAut.conj g).toMonoidHom
  let A := Source.starImage H Ug
  let D := s.image (Source.DH U Ug A₁)
  let S := s.image A₁
  change 4 ≤ fixedCodim act.representation A at hlower
  have hUV : U ≤ Source.VH H V := conjugateSpanBy_mono hflag le_rfl
  have hUgH : Ug ≤ H := (map_mono hUV).trans hforward
  have hreverse : U ≤ H.map (MulAut.conj g).toMonoidHom :=
    hUV.trans (hback.trans (map_mono ((pCoreIn_le 2 P).trans hPH)))
  have hUA : U ≤ normalizer (A₁ : Set G) := hreverse.trans
    ((s.centralizes_conjugate_line g).trans (centralizer_le_normalizer _))
  have hA₁card : Nat.card A₁ = 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  let eA := (MulAut.conj (QuotientGroup.mk' (pCore 2 H) h)).trans eH
  have hAm : A.map eA.toMonoidHom = tensorPointRadical := by
    change A.map (eH.toMonoidHom.comp (MulAut.conj _).toMonoidHom) = _
    rw [← Subgroup.map_map]
    change ((Source.starImage H Ug).map _).map _ = _
    rw [hsat, ← Seven.LocalGeometry.starImage_conjugate H Vg hforward h]
    exact hmark
  have hrank : rank A = 2 := by
    rw [← rank_map_injective eA.toMonoidHom eA.injective, hAm]
    exact tensorPointRadical_rank_two
  obtain ⟨a,ha,b,hb,hgenerators⟩ := radical_two_generators eA A hAm
  have hD : Module.finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁) ⧸ D) ≤ 2 := by
    have hh := s.critical_bound Ug A₁ hUgH hfaith hcritical
    exact hh.trans hrank.le
  have hline := s.critical_line_displacement Ug A₁ hUA hA₁card
  have hupp := two_generator_bound act.representation A a b ha hb hgenerators D S hline.2
  have hsdim : Module.finrank (ZMod 2) S ≤ 1 := hline.1
  have hDeq : Module.finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁) ⧸ D) = 2 := by omega
  -- An external order-two line has zero image, contradicting codimension four.
  have hA₁U : A₁ ≤ U := by
    by_contra hn
    have hz : S = ⊥ := s.image_eq_bot_of_not_le A₁ hA₁card hn
    have hzero : Module.finrank (ZMod 2) S = 0 := by rw [hz, finrank_bot]
    omega
  let Ur := U.map (MulAut.conj g⁻¹).toMonoidHom
  let Vr := (Source.VH H V).map (MulAut.conj g⁻¹).toMonoidHom
  have hUrVr : Ur ≤ Vr := map_mono hUV
  have hVrP : Vr ≤ P.pCoreIn 2 := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hback
    rwa [conjugate_inverse_cancel] at hh
  have hVrH : Vr ≤ H := hVrP.trans ((pCoreIn_le 2 P).trans hPH)
  have hrevRank : rank (Source.starImage H Ur) = 2 :=
    (reversed_rank_and_codimension s g hUgH hreverse hfaith).1.trans hDeq
  have hradCard : Nat.card tensorPointRadical = 4 := by
    rw [tensorPointRadical, card_map_of_injective
      (show Function.Injective componentInclusion from fun _ _ hh => congrArg Prod.fst hh),
      card_pointRadical]
  have hPcard : Nat.card (Source.starImage H (P.pCoreIn 2)) = 4 := by
    rw [← card_map_of_injective (f := eH.toMonoidHom) eH.injective, hparabolic, hradCard]
  have hVrCard : Nat.card (Source.starImage H Vr) ≤ 4 := by
    rw [← hPcard]
    exact Nat.card_le_card_of_injective
      (Subgroup.inclusion (map_mono (comap_mono hVrP))) (Subgroup.inclusion_injective _)
  have hUrCard : 4 ≤ Nat.card (Source.starImage H Ur) := by
    have hh := Nat.pow_log_le_self 2 (Nat.card_ne_zero.mpr ⟨inferInstance,inferInstance⟩ :
      Nat.card (Source.starImage H Ur) ≠ 0)
    change rank (Source.starImage H Ur) = 2 at hrevRank
    change 2 ^ rank (Source.starImage H Ur) ≤ _ at hh
    simpa only [hrevRank] using hh
  -- Both reverse images lie in the order-four core, and the smaller has rank two.
  have hrevEqual : Source.starImage H Ur = Source.starImage H Vr :=
    eq_of_le_of_card_ge (map_mono (comap_mono hUrVr)) (hVrCard.trans hUrCard)
  have hVrUr : Vr ≤ normalizer (Ur : Set G) := by
    rw [← map_equiv_normalizer_eq]
    exact map_mono ((conjugateSpanBy_le_self hVH).trans s.normalizes)
  have hUUr : U ≤ normalizer (Ur : Set G) := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (hUgH.trans s.normalizes)
    rw [conjugate_inverse_cancel, map_equiv_normalizer_eq] at hh
    exact hh
  have hZUr : V₁ ≤ Ur := (reversed_line_containment U V₁ g).mp hA₁U
  have hc := equal_star_commutator s Ur Vr hUrVr hVrH hVrUr hUUr hZUr hrevEqual
  have hc' := map_mono (f := (MulAut.conj g).toMonoidHom) hc
  rw [map_commutator] at hc'
  have hcancel (B : Subgroup G) :
      (B.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = B := by
    simpa only [inv_inv] using conjugate_inverse_cancel g⁻¹ B
  change ⁅Ug,Vr.map (MulAut.conj g).toMonoidHom⁆ ≤ Ur.map (MulAut.conj g).toMonoidHom at hc'
  rw [hcancel, hcancel] at hc'
  exact source_noncentral H P V V₃ Ug hVH hflag hPH hUgH hgen hseed hnoncentral hc'

private theorem span_conjugate (F H : Subgroup G) (h : H) :
    conjugateSpanBy (F.map (MulAut.conj (h:G)).toMonoidHom) H = conjugateSpanBy F H := by
  have hf : F.map (MulAut.conj (h:G)).toMonoidHom ≤ conjugateSpanBy F H := by
    rintro _ ⟨f,hf,rfl⟩
    exact le_normalizer_iff.mp (le_normalizer_conjugateSpanBy F H) h h.property
      f (le_conjugateSpanBy F H hf)
  apply le_antisymm (conjugateSpanBy_le hf (le_normalizer_conjugateSpanBy F H))
  apply conjugateSpanBy_le _ (le_normalizer_conjugateSpanBy _ H)
  intro f hf
  have hh := le_normalizer_iff.mp (le_normalizer_conjugateSpanBy
    (F.map (MulAut.conj (h:G)).toMonoidHom) H) (h:G)⁻¹ (H.inv_mem h.property)
    ((MulAut.conj (h:G)) f) (le_conjugateSpanBy _ H (mem_map_of_mem _ hf))
  simpa only [MulAut.conj_apply, inv_inv, inv_mul_cancel_left, mul_inv_cancel_right,
    mul_assoc, inv_mul_cancel, mul_one] using hh

private theorem tensor_section_faithful {J W : Type*} [Group J]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) J W) (L N : Subrepresentation ρ)
    (eH : J ≃* TensorGroup)
    (e : (sectionRepresentation ρ L N).Equiv (naturalTensor.comp eH.toMonoidHom))
    (hf : Function.Injective naturalTensor) : Function.Injective ρ := by
  intro a b hab
  apply eH.injective
  apply hf
  apply LinearMap.ext
  intro w
  obtain ⟨v,rfl⟩ := e.toLinearEquiv.surjective w
  have he (c : J) (v) : e.toLinearEquiv (sectionRepresentation ρ L N c v) =
      naturalTensor (eH c) (e.toLinearEquiv v) :=
    Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap c v
  rw [← he a v, ← he b v]
  congr 1
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change sectionRepresentation ρ L N a ((sectionLower ρ L N).toSubmodule.mkQ v) =
      sectionRepresentation ρ L N b ((sectionLower ρ L N).toSubmodule.mkQ v)
    rw [sectionRepresentation_mk, sectionRepresentation_mk]
    apply congrArg (sectionLower ρ L N).toSubmodule.mkQ
    exact Subtype.ext (LinearMap.congr_fun hab v.val)

private theorem tensor_lower [FiniteDimensional (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]
    (act : SourceAction H V₃ V₁) (L N : Subrepresentation act.representation)
    (eH : Source.Hstar H ≃* TensorGroup)
    (e : (sectionRepresentation act.representation L N).Equiv (naturalTensor.comp eH.toMonoidHom))
    (A B : Subgroup G) (hBH : B ≤ H) (h : H)
    (hsat : Source.starImage H A = Source.starImage H B)
    (hmark : (Source.starImage H (B.map (MulAut.conj (h:G)).toMonoidHom)).map
      eH.toMonoidHom = tensorPointRadical)
    (hfixed : fixedCodim naturalTensor tensorPointRadical = 4) :
    4 ≤ fixedCodim act.representation (Source.starImage H A) := by
  let σ := sectionRepresentation act.representation L N
  have he : fixedCodim σ (Source.starImage H (B.map (MulAut.conj (h:G)).toMonoidHom)) = 4 := by
    rw [fixedCodim_map_equivariant σ naturalTensor eH.toMonoidHom e.toLinearEquiv
      e.toIntertwiningMap.isIntertwining, hmark, hfixed]
  rw [Seven.LocalGeometry.starImage_conjugate H B hBH h, fixedCodim_map_conj] at he
  rw [hsat]
  exact he.symm.le.trans (fixedCodim_section_le act.representation L N (Source.starImage H B))

/-- The saturated branch of the marked tensor critical-pair argument is
impossible. All source groups are literal conjugate spans and all starred
groups are their images in H/O₂(H). The two tensor facts are the independent
model inputs; the parent supplies the marked chief section and geometry. -/
theorem source_saturated_pair_false [Finite G]
    [FiniteDimensional (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]
    (act : SourceAction H V₃ V₁)
    (K L₀ X L₁ T V : Subgroup G) (g : G) (h : H)
    (eH : Source.Hstar H ≃* TensorGroup)
    (L N : Subrepresentation act.representation)
    (hchief : IsNaturalTensorChiefSection act.representation eH L N)
    (htensor_faithful : Function.Injective naturalTensor)
    (htensor_fixed : fixedCodim naturalTensor tensorPointRadical = 4)
    (hV : V ≤ H) (hflag : V₃ ≤ V) (_hflag_index : V₃.relIndex V = 2)
    (_hline : V₁ ≤ V₃) (hcard : Nat.card V₁ = 2)
    (hcentral : H ≤ centralizer (V₁ : Set G))
    (_hL₀ : L₀ ≤ L₁) (_hX : X ≤ L₁)
    (_hL₀mark : (Source.starImage H L₀).map eH.toMonoidHom ≤
      (⊤ : Subgroup BinaryLinearThree.Group).prod ⊥)
    (_hXmark : (Source.starImage H X).map eH.toMonoidHom ≤
      (⊥ : Subgroup BinaryLinearThree.Group).prod ⊤)
    (_hL₀seed : ⁅L₀,V₃⁆ ≤ V₁) (_hXseed : V₃ ≤ ⁅X,V₃⁆ ⊔ V₁)
    (hPH : L₁ ⊔ T ≤ H) (hH : H = K ⊔ (L₁ ⊔ T))
    (hK : (K.subgroupOf H).Normal) (hres : pResidual 2 (K.subgroupOf H) = ⊤)
    (hqs : Theory.GroupTheory.IsQuasisimple (Source.starImage H K))
    (hseed : ⁅L₁ ⊔ T,V⁆ ≤ Source.UH H V₃)
    (hnoncentral : ¬ ⁅Source.VH H V,H⁆ ≤ Source.UH H V₃)
    (hforward : (Source.VH H V).map (MulAut.conj g).toMonoidHom ≤ H)
    (hback : Source.VH H V ≤ ((L₁ ⊔ T).pCoreIn 2).map (MulAut.conj g).toMonoidHom)
    (hplace : ((Source.VH H V).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj (h:G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2)
    (_hcentralizer : ⁅Source.HC H V₃,Source.VH H V⁆ ≤ V₁)
    (_hdisjoint : Disjoint V₁ (V₁.map (MulAut.conj g).toMonoidHom))
    (_hseed_noncentral : ¬ ⁅(Source.UH H V₃).map (MulAut.conj g).toMonoidHom,V⁆ ≤
      V₁.map (MulAut.conj g).toMonoidHom)
    (_hcommute : ⁅Source.DH (Source.UH H V₃)
        ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)
        (V₁.map (MulAut.conj g).toMonoidHom),
      Source.Dgamma ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)
        (Source.UH H V₃) V₁⁆ = ⊥)
    (_hparabolic_group : (Source.starImage H (L₁ ⊔ T)).map eH.toMonoidHom =
      Matrix.PSL3Two.pointParabolicSL.prod ⊤)
    (_hline_commutators :
      ⁅(Source.UH H V₃).map (MulAut.conj g).toMonoidHom,
        Source.EH (Source.VH H V) ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)
          (V₁.map (MulAut.conj g).toMonoidHom)⁆ ≤ V₁.map (MulAut.conj g).toMonoidHom ∧
      ⁅Source.UH H V₃, Source.Egamma ((Source.VH H V).map (MulAut.conj g).toMonoidHom)
        (Source.UH H V₃) V₁⁆ ≤ V₁)
    (hparabolic : (Source.starImage H ((L₁ ⊔ T).pCoreIn 2)).map
      eH.toMonoidHom = tensorPointRadical)
    (hcritical : Nat.log 2 ((Source.DH (Source.UH H V₃)
        ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)
        (V₁.map (MulAut.conj g).toMonoidHom)).relIndex (Source.UH H V₃)) ≤
      Nat.log 2 ((Source.Dgamma ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)
        (Source.UH H V₃) V₁).relIndex ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)))
    (hmark : (Source.starImage H (((Source.VH H V).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj (h:G)).toMonoidHom)).map eH.toMonoidHom = tensorPointRadical)
    (hsaturated : Source.starImage H ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom) =
      Source.starImage H ((Source.VH H V).map (MulAut.conj g).toMonoidHom)) : False := by
  obtain ⟨_,⟨e⟩⟩ := hchief
  have hfaith := tensor_section_faithful act.representation L N eH e htensor_faithful
  have hlower := tensor_lower H V₃ V₁ act L N eH e _ _ hforward h hsaturated hmark htensor_fixed
  let s := sourceSection H V₃ V₁ act hcentral
  let Ug := (Source.UH H V₃).map (MulAut.conj g).toMonoidHom
  let Uα := Ug.map (MulAut.conj (h:G)).toMonoidHom
  let Vg := (Source.VH H V).map (MulAut.conj g).toMonoidHom
  have hUgVg : Ug ≤ Vg := map_mono (conjugateSpanBy_mono hflag le_rfl)
  have hUgH : Ug ≤ H := hUgVg.trans hforward
  have hUαP : Uα ≤ (L₁ ⊔ T).pCoreIn 2 := (map_mono hUgVg).trans hplace
  have hUαH : Uα ≤ H := hUαP.trans ((pCoreIn_le 2 (L₁ ⊔ T)).trans hPH)
  have hUαmark : (Source.starImage H Uα).map eH.toMonoidHom = tensorPointRadical := by
    rw [Seven.LocalGeometry.starImage_conjugate H Ug hUgH h, hsaturated,
      ← Seven.LocalGeometry.starImage_conjugate H Vg hforward h]
    exact hmark
  have hnot : ¬ Uα ≤ Source.Dgamma Uα (Source.UH H V₃) V₁ := by
    intro hh
    have hi := s.Dgamma_relIndex Uα hUαH hfaith
    rw [relIndex_eq_one.mpr hh] at hi
    have hbot := card_eq_one.mp hi.symm
    have hm := hUαmark
    rw [hbot, Subgroup.map_bot] at hm
    have hr := tensorPointRadical_rank_two
    rw [← hm, Representation.BinaryOffender.rank_bot] at hr
    omega
  -- Apply the actual earlier component generation theorem, checking its denominator.
  have hgen := CriticalGeometry.generation_of_edge_two_core H K (L₁ ⊔ T) Uα
    (Source.UH H V₃) V₁ hH hK hres hqs hUαP
    (s.Dgamma_eq_inf_core Uα hUαH hfaith) Uα le_rfl hnot
  rw [span_conjugate Ug H h] at hgen
  exact saturated_core H V₃ V₁ act hcentral V (L₁ ⊔ T) g h hV hflag hPH
    hforward hback hcard hgen hseed hnoncentral hfaith eH hmark hsaturated hparabolic hcritical hlower

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical.SaturatedPair
