module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalQuadratic
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.SteinbergSmallMovement
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.Dimensions
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupAction.CyclicQuotientSmallLayer
public import Theory.GroupTheory.SubgroupPartitionCounting

/-!
# Ambient displacement on the literal U_L/V section

In the full-denominator branch V is not contained in Qγ: otherwise the
commutator [V,Uγ]=V₁ lies in A₁, contrary to the disjoint endpoint lines.
If U_L has image of order at most four modulo Qγ, then
B=V(U_L∩Qγ) has index at most two in U_L. Conjugation by Uγ moves B/V
into A₁V/V, of order at most two. The cyclic displacement bound therefore
gives fixed codimension at most two on the original U_L/V action.

For the Steinberg exclusion there is a shorter sufficient bound. Mutual
normalization puts [U_L,u] inside Uγ for each u in Uγ. The whole natural
module or its augmentation cover has order at most 64, and V₁ lies in
Uγ∩V. Its image modulo V therefore has dimension at most five. A
noncentral element of Uγ gives a barred involution, whose displacement on
the Steinberg tensor is at least six. Thus no Steinberg quotient exists,
without assuming the sharper endpoint image bound above.

AmbientComparison applies this to the original local planes and constructs
all parabolic markings. Their construction, the remaining permutation and
13.4.1 arguments stay with qt-d-138-a6-endgame-source; earlier ordinary
setup stays with qt-d-138-six-g2-source. This does not yet prove 13.8.33.
Source: Aschbacher--Smith, proof of 13.8.33, printed p.967.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionQuotients TransvectionQuotients.FourLocalFactors
open Representation.BinaryOffender.NaturalTensor

private theorem section_displacement_bound {G A : Type*} [Group G] [Finite G] [Group A]
    (R Z P : Subgroup G) [(Z.subgroupOf R).Normal]
    [IsElementaryAbelian 2 (R ⧸ Z.subgroupOf R)]
    (π : P →* A) (hPR : P ≤ normalizer (R : Set G))
    (ρ : Representation (ZMod 2) A (Additive (R ⧸ Z.subgroupOf R)))
    (hρ : SectionConjugationAlong P R Z π hPR ρ)
    (p : P) :
    operatorFixedCodim (ρ (π p)) ≤
      Module.finrank (ZMod 2) (sectionImage R Z ⁅R, zpowers (p : G)⁆) := by
  apply Submodule.finrank_mono
  rintro _ ⟨x, rfl⟩
  obtain ⟨r, hr⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf R) x.toMul
  have hx : Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf R) r) = x := hr
  rw [← hx]
  change ρ (π p) (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf R) r)) -
    Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf R) r) ∈ _
  rw [hρ]
  have hc : ⁅(p : G), (r : G)⁆ ∈ ⁅R,zpowers (p : G)⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator (mem_zpowers _) r.property
  have hcR : ⁅(p : G), (r : G)⁆ ∈ R := by
    exact le_normalizer_iff_commutator_le_left.mp
      (zpowers_le.mpr (hPR p.property)) hc
  refine ⟨⟨⁅(p : G),(r : G)⁆,hcR⟩,hc,?_⟩
  change Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf R) _) =
    Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf R) _ /
      QuotientGroup.mk' (Z.subgroupOf R) r)
  rw [← map_div]
  congr 2
  apply Subtype.ext
  simp only [commutatorElement_def,div_eq_mul_inv]
  rfl

private theorem section_commutator_index_bound {G A : Type*} [Group G] [Finite G] [Group A]
    (R D Z E P : Subgroup G) [(Z.subgroupOf R).Normal]
    [IsElementaryAbelian 2 (R ⧸ Z.subgroupOf R)]
    (hDR : D ≤ R) (hZR : Z ≤ R) (hER : E ≤ R)
    (π : P →* A) (hPR : P ≤ normalizer (R : Set G))
    (ρ : Representation (ZMod 2) A (Additive (R ⧸ Z.subgroupOf R)))
    (_hρ : SectionConjugationAlong P R Z π hPR ρ)
    (p : P) (hindex : D.relIndex R ≤ 2)
    (hsmall : Z.relIndex E ≤ 2) (hcomm : ⁅D, zpowers (p : G)⁆ ≤ E) :
    Z.relIndex (⁅R,zpowers (p : G)⁆ ⊔ Z) ≤ 4 := by
  have hab : ⁅R,R⁆ ≤ Z := by
    have hh := (Normal.quotient_commutative_iff_commutator_le (N := Z.subgroupOf R)).mp
      (inferInstance : IsMulCommutative (R ⧸ Z.subgroupOf R))
    have hm : (_root_.commutator R).map R.subtype = ⁅R,R⁆ := by
      rw [_root_.commutator_def,map_commutator,← MonoidHom.range_eq_map,range_subtype]
    rw [← hm]
    exact (map_mono hh).trans_eq (map_subgroupOf_eq_of_le hZR)
  apply quotient_commutator_relIndex_le_four_of_index_two_small_layer
    R D Z E hDR hZR hER inferInstance hab (p : G) (hPR p.property) _ hsmall hcomm
  rw [← relIndex_mul_card_of_le hDR]
  exact Nat.mul_le_mul_right _ hindex


private theorem section_small_displacement {G A : Type*} [Group G] [Finite G] [Group A]
    (R D Z E P : Subgroup G) [(Z.subgroupOf R).Normal]
    [IsElementaryAbelian 2 (R ⧸ Z.subgroupOf R)]
    (hDR : D ≤ R) (hZR : Z ≤ R) (hER : E ≤ R)
    (π : P →* A) (hPR : P ≤ normalizer (R : Set G))
    (ρ : Representation (ZMod 2) A (Additive (R ⧸ Z.subgroupOf R)))
    (hρ : SectionConjugationAlong P R Z π hPR ρ)
    (p : P) (hindex : D.relIndex R ≤ 2)
    (hsmall : Z.relIndex E ≤ 2) (hcomm : ⁅D, zpowers (p : G)⁆ ≤ E) :
    operatorFixedCodim (ρ (π p)) ≤ 2 := by
  have hC : ⁅R,zpowers (p : G)⁆ ≤ R :=
    le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr (hPR p.property))
  have hb := section_commutator_index_bound R D Z E P hDR hZR hER π hPR ρ hρ p hindex hsmall hcomm
  have hr : Z.relIndex (⁅R,zpowers (p : G)⁆ ⊔ Z) = Z.relIndex ⁅R,zpowers (p : G)⁆ := by
    have hh := relIndex_sup_right ((⁅R,zpowers (p : G)⁆).subgroupOf R) (Z.subgroupOf R)
    rw [← subgroupOf_sup hC hZR,relIndex_subgroupOf (sup_le hC hZR),relIndex_subgroupOf hC] at hh
    exact hh
  rw [hr, ← pow_finrank_sectionImage R Z _ hC] at hb
  have hd : Module.finrank (ZMod 2) (sectionImage R Z ⁅R,zpowers (p : G)⁆) ≤ 2 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
  exact (section_displacement_bound R Z P π hPR ρ hρ p).trans hd


private theorem index_two_join_of_index_four {G : Type*} [Group G] [Finite G]
    (R V Q : Subgroup G) (hVR : V ≤ R) (hV : ¬ V ≤ Q)
    (hi : Q.relIndex R ≤ 4) : (V ⊔ (R ⊓ Q)).relIndex R ≤ 2 := by
  let I := R ⊓ Q
  let B := V ⊔ I
  have hBR : B ≤ R := sup_le hVR inf_le_left
  have hn : I.relIndex B ≠ 1 := by
    intro he
    exact hV ((le_sup_left.trans (relIndex_eq_one.mp he)).trans inf_le_right)
  have hp : I.relIndex B ≠ 0 := index_ne_zero_of_finite
  have hm := relIndex_mul_relIndex I B R le_sup_right hBR
  have hI : I.relIndex R ≤ 4 := by simpa only [I,inf_relIndex_left] using hi
  have ht : 2 ≤ I.relIndex B := by omega
  have hh := Nat.mul_le_mul_right (B.relIndex R) ht
  change B.relIndex R ≤ 2
  nlinarith

open TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H L₂ : Subgroup G}

private theorem endpoint_core_commutator
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) :
    ⁅c.Qgamma, c.Ugamma V₃⁆ ≤ c.Aone V₁ := by
  have hh := map_mono (f := (MulAut.conj (c.gb : G)).toMonoidHom)
    h.commutator_UH_QH_le_point
  rw [map_commutator,commutator_comm] at hh
  exact hh

/-- The original natural module escapes the transported two-core. -/
theorem full_denominators_seed_not_le_endpoint_core
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃) :
    ¬ V ≤ c.Qgamma := by
  intro hV
  have hm := (ComponentSieve.SixAndG2.Overgroup.full_denominators_commutator d h c hDH hDg).2.1
  have hz : V₁ ≤ c.Aone V₁ :=
    hm.symm.le.trans ((commutator_mono hV le_rfl).trans (endpoint_core_commutator h c))
  have he : V₁ = ⊥ := le_bot_iff.mp
    ((le_inf le_rfl hz).trans (local_earlierGeometry d h c).lines_disjoint.le)
  have hc := d.line_card
  rw [he,card_bot] at hc
  contradiction


/-- Every element of Uγ moves at most two dimensions in the literal section,
provided its endpoint core intersection has index at most four. -/
theorem full_denominators_small_displacement_along
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hab : IsMulCommutative (Source.UL L H V₃))
    (hVUL : V ≤ Source.UL L H V₃)
    [(V.subgroupOf (Source.UL L H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.ULsection L H V₃ V)]
    {A : Type*} [Group A] (π : (L ⊔ (T : Subgroup G) : Subgroup G) →* A)
    (hn : L ⊔ (T : Subgroup G) ≤ normalizer (Source.UL L H V₃ : Set G))
    (ρ : Representation (ZMod 2) A (Additive (Source.ULsection L H V₃ V)))
    (hρ : SectionConjugationAlong (L ⊔ (T : Subgroup G)) (Source.UL L H V₃) V π hn ρ)
    (hi : c.Qgamma.relIndex (Source.UL L H V₃) ≤ 4)
    (p : (L ⊔ (T : Subgroup G) : Subgroup G)) (hp : (p : G) ∈ c.Ugamma V₃) :
    operatorFixedCodim (ρ (π p)) ≤ 2 := by
  let _ := hab
  let R := Source.UL L H V₃
  let B := V ⊔ (R ⊓ c.Qgamma)
  let E := V ⊔ c.Aone V₁
  have hBR : B ≤ R := sup_le hVUL inf_le_left
  have hAR : c.Aone V₁ ≤ R :=
    (endpoint_commutator d h c hDH hDg hcentral).2.trans (le_conjugateSpanBy _ _)
  have hER : E ≤ R := sup_le hVUL hAR
  have hindex : B.relIndex R ≤ 2 := index_two_join_of_index_four R V c.Qgamma hVUL
    (full_denominators_seed_not_le_endpoint_core d h c hDH hDg) hi
  have hsmall : V.relIndex E ≤ 2 := by
    have hh := relIndex_sup_right ((c.Aone V₁).subgroupOf R) (V.subgroupOf R)
    rw [← subgroupOf_sup hAR hVUL,relIndex_subgroupOf (sup_le hAR hVUL),
      relIndex_subgroupOf hAR] at hh
    have he : V.relIndex E = V.relIndex (c.Aone V₁) := by
      simpa only [E,sup_comm] using hh
    rw [he]
    have hb : V.relIndex (c.Aone V₁) ≤ Nat.card (c.Aone V₁) := Nat.le_of_dvd Nat.card_pos (relIndex_dvd_card _ _)
    have hc : Nat.card (c.Aone V₁) = 2 := by
      change Nat.card (V₁.map (MulAut.conj (c.gb : G)).toMonoidHom) = 2
      rw [card_map_of_injective (MulAut.conj (c.gb : G)).injective,d.line_card]
    exact hb.trans_eq hc
  have hBE : B ≤ normalizer (E : Set G) :=
    ((hBR.trans (le_centralizer R)).trans (centralizer_le hER)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcomm : ⁅B,zpowers (p : G)⁆ ≤ E := by
    apply commutator_sup_le_of_relative_normal B V (R ⊓ c.Qgamma)
      (zpowers (p : G)) E hBE le_sup_left le_sup_right
    · exact (commutator_mono le_rfl (zpowers_le.mpr hp)).trans
        (((ComponentSieve.SixAndG2.Overgroup.full_denominators_commutator d h c hDH hDg).2.1.le).trans
          ((d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)).trans le_sup_left))
    · exact (commutator_mono inf_le_right (zpowers_le.mpr hp)).trans
        ((endpoint_core_commutator h c).trans le_sup_right)
  exact section_small_displacement R B V E (L ⊔ (T : Subgroup G)) hBR hVUL hER
    π hn ρ hρ p hindex hsmall hcomm


/-- Every element of Uγ moves at most two dimensions in the literal section,
provided its endpoint core intersection has index at most four. -/
theorem full_denominators_small_displacement
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hab : IsMulCommutative (Source.UL L H V₃))
    (s : SectionStructure.Data L H (T : Subgroup G) (sourceOne L T V₁) L₂ V V₂ V₃)
    (hi : c.Qgamma.relIndex (Source.UL L H V₃) ≤ 4)
    (p : (L ⊔ (T : Subgroup G) : Subgroup G)) (hp : (p : G) ∈ c.Ugamma V₃) :
    let _ := s.normal; let _ := s.elementary;
    operatorFixedCodim (s.action ((barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict p)) ≤ 2 := by
  let _ := s.normal
  let _ := s.elementary
  exact full_denominators_small_displacement_along d h c hDH hDg hcentral hab s.contains
    (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict s.normalizes_UL
    s.action s.conjugation hi p hp


variable [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The opposite module supplies a nonidentity involution in the literal bar image. -/
theorem full_denominators_bar_mover
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (e : (barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).range ≃* Equiv.Perm (Fin 6)) :
    ∃ p : (L ⊔ (T : Subgroup G) : Subgroup G), (p : G) ∈ c.Ugamma V₃ ∧
      orderOf (e ((barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).rangeRestrict p)) = 2 := by
  classical
  let : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  obtain ⟨hc,hm,_⟩ := ComponentSieve.SixAndG2.Overgroup.full_denominators_commutator d h c hDH hDg
  have hUC : c.Ugamma V₃ ≤ centralizer (Source.UH H V₃ : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rwa [commutator_comm]
  have hUH : c.Ugamma V₃ ≤ H :=
    (map_mono (conjugateSpanBy_mono d.seed_le le_rfl)).trans
      (local_earlierGeometry d h c).Vgamma_H
  have hUQ : c.Ugamma V₃ ≤ Source.QH H := by
    apply le_trans _ h.kernel_UH_eq_QH.le
    intro u hu
    exact (h.mem_kernel_iff h.UH_le_H).mpr ⟨hUH hu,fun v hv => by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hUC hu v hv)]
      exact V₁.one_mem⟩
  have hUP : c.Ugamma V₃ ≤ L ⊔ (T : Subgroup G) :=
    hUQ.trans (h.QH_le_T.trans le_sup_right)
  have hex : ∃ u ∈ c.Ugamma V₃, u ∉ centralizer (V : Set G) := by
    by_contra! hn
    have hz : V₁ = ⊥ := hm.symm.trans (by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hn)
    have hh := d.line_card
    rw [hz,card_bot] at hh
    contradiction
  obtain ⟨u,hu,hnu⟩ := hex
  let p : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨u,hUP hu⟩
  let π := (barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).rangeRestrict
  have hne : e (π p) ≠ 1 := by
    intro he
    have hb : π p = 1 := e.injective (he.trans (map_one e).symm)
    have hb' : p ∈ (barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).ker :=
      congrArg Subtype.val hb
    rw [barMap_ker] at hb'
    exact hnu hb'
  have hp2 : p ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian u hu)
  have hb2 : e (π p) ^ 2 = 1 := by rw [←map_pow,←map_pow,hp2,map_one,map_one]
  exact ⟨p,hu,orderOf_eq_prime hb2 hne⟩

/-- Construct a nonidentity barred involution with the ambient displacement bound. -/
theorem full_denominators_small_mover
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hab : IsMulCommutative (Source.UL L H V₃))
    (s : SectionStructure.Data L H (T : Subgroup G) (sourceOne L T V₁) L₂ V V₂ V₃)
    (hi : c.Qgamma.relIndex (Source.UL L H V₃) ≤ 4)
    (e : (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).range ≃* Equiv.Perm (Fin 6)) :
    let _ := s.normal; let _ := s.elementary;
    ∃ b : (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).range,
      orderOf (e b) = 2 ∧ operatorFixedCodim (s.action b) ≤ 2 := by
  let _ := s.normal
  let _ := s.elementary
  obtain ⟨p,hp,ho⟩ := full_denominators_bar_mover d h c hDH hDg e
  exact ⟨(barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict p, ho,
    full_denominators_small_displacement d h c hDH hDg hcentral hab s hi p hp⟩

/-- The whole natural module or its augmentation cover bounds U_H by 64.
The fixed line of the cover is retained in this count. -/
theorem compatible_UH_card_le_sixtyFour
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : A6Endgame.IntersectionBalance.CompatibleModel H V₃ V₁ a e) :
    Nat.card (Source.UH H V₃) ≤ 64 := by
  have hd : Module.finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) ≤ 5 := by
    rcases A6Endgame.IntersectionBalance.CompatibleModel.action_cases H V₃ V₁ a e model with ⟨F,_⟩ | ⟨F,_⟩
    · rw [F.finrank_eq, BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
      decide
    · rw [F.finrank_eq]
      change Module.finrank (ZMod 2) (BinaryPermutation.core (Fin 6)) ≤ 5
      rw [BinaryPermutation.finrank_core]
      decide
  have ht : Nat.card (Source.Utilde H V₃ V₁) ≤ 32 := by
    change Nat.card (Additive (Source.Utilde H V₃ V₁)) ≤ 32
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide) hd
  have hc := relIndex_mul_card_of_le (d.line_le_uh H)
  rw [d.line_card] at hc
  change Nat.card (Source.Utilde H V₃ V₁) * 2 = Nat.card (Source.UH H V₃) at hc
  omega

/-- Mutual normalization alone bounds displacement by five. This is enough
for the Steinberg exclusion, whose involution displacement is at least six,
and does not require the sharper point-core image bound. -/
theorem full_denominators_span_displacement
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : A6Endgame.IntersectionBalance.CompatibleModel H V₃ V₁ a e)
    (hab : IsMulCommutative (Source.UL L H V₃))
    (s : SectionStructure.Data L H (T : Subgroup G) (sourceOne L T V₁) L₂ V V₂ V₃)
    (p : (L ⊔ (T : Subgroup G) : Subgroup G)) (hp : (p : G) ∈ c.Ugamma V₃) :
    let _ := s.normal; let _ := s.elementary;
    operatorFixedCodim (s.action ((barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict p)) ≤ 5 := by
  let _ := s.normal
  let _ := s.elementary
  let R := Source.UL L H V₃
  let I := R ⊓ c.Ugamma V₃
  have hline : V₁ ≤ V := d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)
  have hI : V₁ ≤ I := le_inf (hline.trans s.contains)
    (ComponentSieve.SixAndG2.Overgroup.full_denominators_commutator d h c hDH hDg).2.2
  have hcard : Nat.card (c.Ugamma V₃) ≤ 64 := by
    change Nat.card ((Source.UH H V₃).map (MulAut.conj (c.gb : G)).toMonoidHom) ≤ 64
    rw [card_map_of_injective (MulAut.conj (c.gb : G)).injective]
    exact compatible_UH_card_le_sixtyFour d a e model
  have hIcard : Nat.card I ≤ 64 := (card_le_of_le inf_le_right).trans hcard
  have hmul := relIndex_mul_card_of_le hI
  rw [d.line_card] at hmul
  have hi : V₁.relIndex I ≤ 32 := by omega
  have hvi : V.relIndex I ≤ 32 :=
    (relIndex_le_of_le_left hline index_ne_zero_of_finite).trans hi
  have hdim : Module.finrank (ZMod 2) (sectionImage R V I) ≤ 5 := by
    rw [← pow_finrank_sectionImage R V I inf_le_left] at hvi
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hvi
  have hcomm : ⁅R,zpowers (p : G)⁆ ≤ I :=
    (commutator_mono le_rfl (zpowers_le.mpr hp)).trans
      (full_denominators_span_quadratic d h c hH hDH hDg hcentral hab).2.2.1
  have hsub : sectionImage R V ⁅R,zpowers (p : G)⁆ ≤ sectionImage R V I := by
    rintro _ ⟨r,hr,rfl⟩
    exact ⟨r,hcomm hr,rfl⟩
  exact (section_displacement_bound R V (L ⊔ (T : Subgroup G))
    (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict
    s.normalizes_UL s.action s.conjugation p).trans ((Submodule.finrank_mono hsub).trans hdim)

/-- No Steinberg quotient of the literal section can survive mutual
normalization with the whole source module, including the cover branch. -/
theorem full_denominators_no_tensor_quotient
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : A6Endgame.IntersectionBalance.CompatibleModel H V₃ V₁ a e)
    (hab : IsMulCommutative (Source.UL L H V₃))
    (s : SectionStructure.Data L H (T : Subgroup G) (sourceOne L T V₁) L₂ V V₂ V₃)
    (eb : (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).range ≃* Equiv.Perm (Fin 6)) :
    let _ := s.normal; let _ := s.elementary;
    ∀ q : s.action.IntertwiningMap (BinaryAlternatingSix.tensorAction.comp eb.toMonoidHom),
      ¬ Function.Surjective q := by
  let _ := s.normal
  let _ := s.elementary
  change ∀ q : s.action.IntertwiningMap (BinaryAlternatingSix.tensorAction.comp eb.toMonoidHom),
    ¬ Function.Surjective q
  intro q hq
  obtain ⟨p,hp,ho⟩ := full_denominators_bar_mover d h c hDH hDg eb
  let b := (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict p
  have hsmall := full_denominators_span_displacement d h c hH hDH hDg hcentral a e model hab s p hp
  have hle := operatorFixedCodim_le_of_surjective (s.action b)
    (BinaryAlternatingSix.tensorAction (eb b)) q.toLinearMap hq
      (IntertwiningMap.isIntertwining _ _ q b)
  have hlo := BinaryAlternatingSix.tensor_involution_displacement_ge_six (eb b) ho
  change operatorFixedCodim (s.action b) ≤ 5 at hsmall
  omega

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
