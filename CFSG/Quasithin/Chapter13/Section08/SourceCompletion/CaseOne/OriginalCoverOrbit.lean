module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalCover

/-!
# The original cover orbit inside the second parabolic

Write B = ⟨V₃^{K₂}⟩ in the five-dimensional cover branch of 13.8.33.
The marked orbit is the even-weight coordinate hyperplane. Every K₂-fixed
vector belongs to it, so the actual U₁ = C_{U_H}(K) lies in B. This uses
K₂ ≤ K, proved from the relative component supplement, and keeps V₁ in
all quotient kernels. The orbit has order 32, V₃U₁ has index two in it,
and the earlier source action doubles B/V₂ to give |U₂| = 256.

The original L₂ action generates U₂ from B. Consequently either U₂ ≤ U₀,
or B∩U₀ = V₃U₁ and B has image of order two modulo U₀. The final theorem
constructs the cover and applies these calculations to the original
full-denominator critical pair. No orbit size, fixed-seed placement or
local intersection is assumed.

The proper-quotient local planes, U₀=U_L, whole-module comparison, 13.4.1
application and strict-denominator assembly remain with
qt-d-138-a6-endgame-source. The earlier ordinary setup remains with
qt-d-138-six-g2-source; the earlier 13.5.4 and 13.7.6 inputs stay explicit.
This module does not assert full 13.8.33.

Source: Aschbacher--Smith, 13.8.6(5) and the proof of 13.8.33,
printed pp.948,967, combined manuscript of 1 March 2004.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open TransvectionQuotients TransvectionQuotients.FourLocalFactors
open TransvectionParabolic TransvectionParabolic.RankDoubling
open Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] [Finite G]
  {H V V₁ V₂ V₃ K : Subgroup G}
  [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)]
  [IsElementaryAbelian 2 (Source.UH H V₃)]

private theorem fixed_coordinates_in_orbit (v : BinaryPermutation.core (Fin 6))
    (hv : ∀ k : BinaryFlags.K, BinaryPermutation.coreRepresentation (Fin 6) k.val v = v) :
    v ∈ OrbitModels.orbit := by
  rw [OrbitModels.orbit_eq_coordSpace]
  have h₁ := hv ⟨BinaryFlags.cycle012, by decide⟩
  have h₂ := hv ⟨BinaryFlags.cycle013, by decide⟩
  have hc : ∀ w : Fin 6 → ZMod 2,
      BinaryPermutation.augmentation (Fin 6) w = 0 →
      (∀ i, w (BinaryFlags.cycle012.symm i) = w i) →
      (∀ i, w (BinaryFlags.cycle013.symm i) = w i) → w 4 = w 5 := by decide +kernel
  exact hc v.val v.property (fun i => congrArg (fun z => z.val i) h₁)
    (fun i => congrArg (fun z => z.val i) h₂)

omit [Finite G] in
/-- A vector in the actual cover belongs to the K₂ orbit as soon as its
marked image does, with V₂ retained in the kernel. -/
theorem cover_orbit_membership
    (m : MarkedOrbit.CoverMarking H V₁ V₂ V₃)
    (h12 : V₁ ≤ V₂) (h23 : V₂ ≤ V₃) (h3V : V₃ ≤ V)
    (u : Source.UH H V₃)
    (hu : MarkedOrbit.coordinates H V₁ V₃ m.equiv (Additive.ofMul u) ∈ OrbitModels.orbit) :
    (u : G) ∈ conjugateSpanBy V₃ (Source.K2 H V₂) := by
  let q := OrbitModels.pointSpace.mkQ
  have hm : q (MarkedOrbit.coordinates H V₁ V₃ m.equiv (Additive.ofMul u)) ∈
      (MarkedOrbit.toModel (V := V) m h3V).range := by
    rw [MarkedOrbit.toModel_range m h3V OrbitModels.point_fixed]
    change q (MarkedOrbit.coordinates H V₁ V₃ m.equiv (Additive.ofMul u)) ∈
      Submodule.span (ZMod 2) {v | ∃ k ∈ BinaryFlags.K,
        OrbitModels.pointSpace.mkQ (BinaryPermutation.coreRepresentation (Fin 6) k OrbitModels.seed) = v}
    rw [← OrbitModels.coverOrbit_eq_span]
    exact Submodule.mem_map_of_mem hu
  obtain ⟨b,hb⟩ := hm
  have he : q (MarkedOrbit.coordinates H V₁ V₃ m.equiv
      (Additive.ofMul u - MarkedOrbit.toUH H V V₂ V₃ h3V b)) = 0 := by
    rw [map_sub, map_sub]
    exact sub_eq_zero.mpr hb.symm
  have hmem : (u : G) / b.val.toMul.val ∈ V₂ := by
    exact (MarkedOrbit.coordinates_mem_point m h12
      (Additive.ofMul u - MarkedOrbit.toUH H V V₂ V₃ h3V b)).mp
      ((Submodule.Quotient.mk_eq_zero _).mp he)
  have hv : (u : G) / b.val.toMul.val ∈ conjugateSpanBy V₃ (Source.K2 H V₂) :=
    le_conjugateSpanBy _ _ (h23 hmem)
  simpa using (conjugateSpanBy V₃ (Source.K2 H V₂)).mul_mem hv b.property

omit [Finite G] in
/-- The whole fixed subgroup of K₂ lies in the actual seed orbit. -/
theorem cover_fixed_le_orbit
    (m : MarkedOrbit.CoverMarking H V₁ V₂ V₃)
    (h12 : V₁ ≤ V₂) (h23 : V₂ ≤ V₃) (h3V : V₃ ≤ V) :
    Source.UH H V₃ ⊓ centralizer (Source.K2 H V₂ : Set G) ≤
      conjugateSpanBy V₃ (Source.K2 H V₂) := by
  intro u hu
  apply cover_orbit_membership m h12 h23 h3V ⟨u,hu.1⟩
  apply fixed_coordinates_in_orbit
  intro k
  obtain ⟨a,rfl⟩ := m.actor_surjective k
  rw [← m.intertwines]
  congr 2
  apply Subtype.ext
  change (a : G) * u * (a : G)⁻¹ = u
  rw [mem_centralizer_iff.mp hu.2 a a.property,mul_inv_cancel_right]

/-- The marked three-space modulo V₂ gives the actual orbit order 32. -/
theorem cover_orbit_card
    (m : MarkedOrbit.CoverMarking H V₁ V₂ V₃)
    (h12 : V₁ ≤ V₂) (h23 : V₂ ≤ V₃) (h3V : V₃ ≤ V)
    (hcard : Nat.card V₂ = 4) :
    Nat.card (conjugateSpanBy V₃ (Source.K2 H V₂)) = 32 := by
  have hB : conjugateSpanBy V₃ (Source.K2 H V₂) ≤ Source.U2 H V V₂ :=
    conjugateSpanBy_mono h3V le_rfl
  have hs : sectionImage (Source.U2 H V V₂) V₂
      (conjugateSpanBy V₃ (Source.K2 H V₂)) = W H V V₂ V₃ h3V := by
    rw [W_eq_image_span]
    rfl
  have hd := pow_finrank_sectionImage (Source.U2 H V V₂) V₂
    (conjugateSpanBy V₃ (Source.K2 H V₂)) hB
  rw [hs,MarkedOrbit.cover_finrank h12 h23 h3V m] at hd
  have hc := relIndex_mul_card_of_le (h23.trans (le_conjugateSpanBy V₃ (Source.K2 H V₂)))
  rw [← hd,hcard] at hc
  exact hc.symm


end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne

namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open TransvectionQuotients TransvectionQuotients.FourLocalFactors
open TransvectionParabolic TransvectionParabolic.RankDoubling
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

private theorem cover_component_marking
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hTH : (T : Subgroup G) ≤ H)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6)) :
    Source.K2 H V₂ ≤ K ∧ ∃ eK : Source.starImage H K ≃* alternatingGroup (Fin 6),
      ∀ k : Source.starImage H K, e k = (eK k).val := by
  have hKH : K ≤ H := by
    intro k hk
    change k ∈ (H : Set G)
    rw [hprod]
    exact ⟨k,hk,1,(T : Subgroup G).one_mem,mul_one k⟩
  let _ := hK.perfect
  have hp : IsPPerfect 2 (K.subgroupOf H) := by
    intro N hN hq
    let _ := hN
    have hs : Subsingleton ((K.subgroupOf H) ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent ((K.subgroupOf H) ⧸ N) hq.isNilpotent
    apply eq_top_iff.mpr
    intro k _
    exact (QuotientGroup.eq_one_iff k).mp (Subsingleton.elim _ _)
  have hr : pResidual 2 H = K.subgroupOf H :=
    pResidual_eq_of_subnormal_product (K.subgroupOf H) ((T : Subgroup G).subgroupOf H)
      hK.subnormal hp T.isPGroup'.comap_subtype (by
        intro x
        have hx : (x : G) ∈ (K : Set G) * (T : Set G) := hprod ▸ x.property
        obtain ⟨k,hk,t,ht,he⟩ := hx
        exact ⟨⟨k,hKH hk⟩,hk,⟨t,hTH ht⟩,ht,Subtype.ext he⟩)
  have hi : (Source.starImage H K).map e.toMonoidHom = alternatingGroup (Fin 6) := by
    change ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).map e.toMonoidHom = _
    rw [← hr,map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _),
      map_pResidual_of_surjective 2 _ e.surjective,Equiv.Perm.twoResidual_eq_alternating]
  have hK₂ : Source.K2 H V₂ ≤ K := by
    have hm := embedded_pResidual_mono 2 (show H ⊓ centralizer (V₂ : Set G) ≤ H from inf_le_left)
    rw [hr, map_subgroupOf_eq_of_le hKH] at hm
    exact hm
  refine ⟨hK₂,(e.subgroupMap _).trans (MulEquiv.subgroupCongr hi),fun _ => rfl⟩


/-- The cover orbit and the second parabolic, on their original source groups. -/
theorem original_cover_orbit
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6))
    (hF : ∀ g v, F (tildeRepresentation H _ V₁ a g v) =
      BinaryPermutation.coreRepresentation (Fin 6) (e g) (F v))
    (hp : (quotientSpace (Source.UH H V₃) V₁ V₃).map F.toLinearMap =
      Representation.SixLetterRadicalDisplacement.W)
    (earlier1354 : EarlierCore.Earlier1354 T L V)
    (earlier1376 : Marking.NaturalSection.Earlier1376 L (EarlierCore.localResidual L V₁)
      T (normalizer (V₁ : Set G)) M V₂ V₃ V₁) :
    Source.U1 H K V₃ ≤ conjugateSpanBy V₃ (Source.K2 H V₂) ∧
    Nat.card (conjugateSpanBy V₃ (Source.K2 H V₂)) = 32 ∧
    (V₃ ⊔ Source.U1 H K V₃).relIndex (conjugateSpanBy V₃ (Source.K2 H V₂)) = 2 ∧
    Nat.card (Source.U2 H V V₂) = 256 ∧
    Source.U2 H V V₂ = conjugateSpanBy (conjugateSpanBy V₃ (Source.K2 H V₂))
      (EarlierCore.localResidual L V₂) ∧
    Source.U2 H V V₂ = ⁅Source.U2 H V V₂, EarlierCore.localResidual L V₂⁆ ∧
    Source.U2 H V V₂ ≤ Source.UL L H V₃ := by
  let _ := local_elementary d
  let _ := d.abelian_span
  let _ := SectionStructure.VH_commutative_of_global_span G₁ H V hHz.2.1
  let ρ := tildeRepresentation H _ V₁ a
  have hρ : TransvectionRecognition.IsConjugation H V₃ V₁ ρ :=
    fun x u => congrArg Additive.ofMul (a.conjugation x u)
  let flag : Marking.StandingFlag T L V V₁ V₂ V₃ :=
    ⟨d.normalizes_L,d.normalizes_V,d.line_le_plane,d.plane_le_seed,d.seed_le,
      ⟨d.line_card,d.plane_card,d.seed_card⟩,d.line_stable,d.plane_stable,d.seed_stable⟩
  have natural : Marking.StandingNatural L V (le_sup_left.trans flag.normalizes_V) :=
    ⟨6,Or.inr rfl,d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' _),
      d.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _),d.coordinate,d.conjugation⟩
  let en := (flag.componentSetup (Marking.standing_natural_earlier natural) ⟨eL⟩).extend
  have h₁ : sourceOne L T V₁ = EarlierCore.localResidual L V₁ :=
    EarlierCore.residual_relative_normalizer_eq L T V₁ T.isPGroup' d.normalizes_L d.line_stable
  have hHz' : H ∈ Source.Hz (EarlierCore.localResidual L V₁) T (normalizer (V₁ : Set G)) M := by
    rw [← h₁,← d.first_normalizer]
    exact hHz
  obtain ⟨hK₂,eK,heK⟩ := cover_component_marking (V₂ := V₂) K hK h.T_le_H hprod e
  obtain ⟨_,_,_,hmark,_,_,hI,hres,_,hL₂,hgen,_,_,hcomm₂,hU₂⟩ :=
    Marking.source_marking_and_core T L V V₁ V₂ V₃ M H K flag natural
      earlier1376 earlier1354 hHz' hK hprod ρ hρ eK
      (Or.inr ⟨F,fun k v => (hF k v).trans (by rw [heK]; rfl)⟩)
  have hdim : Module.finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) = 5 :=
    F.finrank_eq.trans (by simpa using BinaryPermutation.finrank_core (Fin 6))
  have hm : Nonempty (MarkedOrbit.CoverMarking H V₁ V₂ V₃) := by
    rcases SourceAssembly.orbitMarking_of_markedParabolic K T ρ hρ hmark with hm | hm
    · obtain ⟨m⟩ := hm
      have hm : Module.finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) = 4 :=
        m.equiv.finrank_eq.trans
          (by simpa using BinaryPermutation.finrank_natural_even (Fin 6) (by decide))
      omega
    · exact hm
  obtain ⟨m⟩ := hm
  have hfixed : Source.U1 H K V₃ ≤ conjugateSpanBy V₃ (Source.K2 H V₂) :=
    (inf_le_inf le_rfl (centralizer_le hK₂)).trans
      (cover_fixed_le_orbit (V := V) m d.line_le_plane d.plane_le_seed d.seed_le)
  have hB := cover_orbit_card m d.line_le_plane d.plane_le_seed d.seed_le d.plane_card
  obtain ⟨_,hseed,_⟩ := original_cover_seed_orders d h c hDH hDg hHz K hK hprod a e F hF hp
  have hi := relIndex_mul_card_of_le (sup_le (le_conjugateSpanBy V₃ (Source.K2 H V₂)) hfixed)
  rw [hseed,hB] at hi
  let ld := SourceAssembly.localData_of_naturalSetup (H := H) en earlier1354 h.T_le_H
    (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) ρ hρ
  obtain ⟨lm⟩ := LocalMarking.nonempty_compatibleMarking en ld
  have hrank := RankDoubling.source_rank_reduction_of_source_data H V V₂ V₃ V₁
    (EarlierCore.localI L V₁ V₂) (EarlierCore.localResidual L V₂) ld lm
    (SourceAssembly.seed_core_commutator (H := H) en h.T_le_H)
    (SourceAssembly.flag_index_two d.plane_le_seed (by decide : (4 : ℕ) ≠ 0)
      d.plane_card d.seed_card) d.plane_card
  rw [MarkedOrbit.cover_finrank d.line_le_plane d.plane_le_seed d.seed_le m] at hrank
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (Source.U2 H V V₂))
  rw [Nat.card_zmod,hrank] at hcard
  have hKL : Source.K2 H V₂ ≤ normalizer (EarlierCore.localResidual L V₂ : Set G) :=
    ((Source.K2_le_centralizer H V₂).trans inf_le_right).trans
      ((Subgroup.centralizer_le_normalizer _).trans
        (local_normality (EarlierCore.localI L V₁ V₂) _ _ V₂ hI hres.symm))
  have heq : Source.U2 H V V₂ = conjugateSpanBy
      (conjugateSpanBy V₃ (Source.K2 H V₂)) (EarlierCore.localResidual L V₂) := by
    apply le_antisymm
    · change conjugateSpanBy V (Source.K2 H V₂) ≤ _
      rw [hgen]
      exact conjugate_span_le_iterated_span _ _ _ hKL
    · exact conjugateSpanBy_le (conjugateSpanBy_mono d.seed_le le_rfl)
        (actor_normalizes_conjugate_span V _ _ ((hL₂.trans le_sup_left).trans d.normalizes_V) hKL)
  exact ⟨hfixed,hB,by omega,hcard,heq,hcomm₂,hU₂⟩

/-- If the second parabolic survives modulo U₀, its seed orbit has precisely
one surviving dimension. This is the literal intersection used in the
proper-quotient branch of 13.8.33. -/
theorem original_cover_orbit_dichotomy
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6))
    (hF : ∀ g v, F (tildeRepresentation H _ V₁ a g v) =
      BinaryPermutation.coreRepresentation (Fin 6) (e g) (F v))
    (hp : (quotientSpace (Source.UH H V₃) V₁ V₃).map F.toLinearMap =
      Representation.SixLetterRadicalDisplacement.W)
    (earlier1354 : EarlierCore.Earlier1354 T L V)
    (earlier1376 : Marking.NaturalSection.Earlier1376 L (EarlierCore.localResidual L V₁)
      T (normalizer (V₁ : Set G)) M V₂ V₃ V₁) :
    Source.U2 H V V₂ ≤ Source.U0 L H K V₃ ∨
      (conjugateSpanBy V₃ (Source.K2 H V₂)) ⊓ Source.U0 L H K V₃ =
        V₃ ⊔ Source.U1 H K V₃ ∧
      (Source.U0 L H K V₃).relIndex (conjugateSpanBy V₃ (Source.K2 H V₂)) = 2 := by
  classical
  obtain ⟨hf,_,hi,_,hgen,_,_⟩ := original_cover_orbit d h c hDH hDg hHz K hK hprod
    eL a e F hF hp earlier1354 earlier1376
  obtain ⟨p⟩ := original_cover_permutation d h c hDH hDg hHz K hK hprod eL a e F hF hp
  by_cases hle : Source.U2 H V V₂ ≤ Source.U0 L H K V₃
  · exact Or.inl hle
  right
  let B := conjugateSpanBy V₃ (Source.K2 H V₂)
  let C := V₃ ⊔ Source.U1 H K V₃
  let N := Source.U0 L H K V₃
  have hCN : C ≤ N := sup_le (d.seed_le.trans p.contains) (le_conjugateSpanBy _ _)
  have hCB : C ≤ B := sup_le (le_conjugateSpanBy _ _) hf
  have hn : ¬ B ≤ N := by
    intro hBN
    apply hle
    rw [hgen]
    apply conjugateSpanBy_le hBN
    have hL₂ : EarlierCore.localResidual L V₂ ≤ L ⊔ (T : Subgroup G) :=
      (EarlierCore.localResidual_le L V₂).trans le_sup_left
    exact hL₂.trans p.normalizes
  have hni : N.relIndex B = 2 := by
    have hd : N.relIndex B ∣ 2 := hi ▸ relIndex_dvd_of_le_left B hCN
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
      (fun he => hn (relIndex_eq_one.mp he))
  have hm := relIndex_mul_relIndex C (B ⊓ N) B (le_inf hCB hCN) inf_le_left
  rw [inf_relIndex_left,hni] at hm
  change C.relIndex B = 2 at hi
  rw [hi] at hm
  have hci : C.relIndex (B ⊓ N) = 1 := by omega
  exact ⟨le_antisymm (relIndex_eq_one.mp hci) (le_inf hCB hCN),hni⟩

/-- Application to the original full-denominator branch: construct the cover
and its orbit, retaining the whole constant-line preimage. -/
theorem full_denominators_cover_orbit
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hH : H = G₁)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (earlier1354 : EarlierCore.Earlier1354 T L V)
    (earlier1376 : Marking.NaturalSection.Earlier1376 L (EarlierCore.localResidual L V₁)
      T (normalizer (V₁ : Set G)) M V₂ V₃ V₁)
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁) :
    Source.U1 H K V₃ ≤ conjugateSpanBy V₃ (Source.K2 H V₂) ∧
    Nat.card (conjugateSpanBy V₃ (Source.K2 H V₂)) = 32 ∧
    (V₃ ⊔ Source.U1 H K V₃).relIndex (conjugateSpanBy V₃ (Source.K2 H V₂)) = 2 ∧
    Nat.card (Source.U2 H V V₂) = 256 ∧
    Source.U2 H V V₂ = conjugateSpanBy (conjugateSpanBy V₃ (Source.K2 H V₂))
      (EarlierCore.localResidual L V₂) ∧
    Source.U2 H V V₂ = ⁅Source.U2 H V V₂, EarlierCore.localResidual L V₂⁆ ∧
    Source.U2 H V V₂ ≤ Source.UL L H V₃ ∧
    (Source.U2 H V V₂ ≤ Source.U0 L H K V₃ ∨
      (conjugateSpanBy V₃ (Source.K2 H V₂)) ⊓ Source.U0 L H K V₃ =
        V₃ ⊔ Source.U1 H K V₃ ∧
      (Source.U0 L H K V₃).relIndex (conjugateSpanBy V₃ (Source.K2 H V₂)) = 2) := by
  obtain ⟨_,F,hF,hp⟩ := full_denominators_abelian_cover d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief
  obtain ⟨hf,hB,hi,hc,hgen,hcomm,hU⟩ :=
    original_cover_orbit d h c hDH hDg hHz K hK hprod eL a e F hF hp earlier1354 earlier1376
  exact ⟨hf,hB,hi,hc,hgen,hcomm,hU,
    original_cover_orbit_dichotomy d h c hDH hDg hHz K hK hprod eL a e F hF hp
      earlier1354 earlier1376⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
