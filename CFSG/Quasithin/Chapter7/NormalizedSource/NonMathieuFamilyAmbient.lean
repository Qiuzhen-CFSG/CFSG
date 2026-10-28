module
public import CFSG.Quasithin.Chapter3.Section01.SourceNumericalComplete
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.StrictSourceNonbinary
public import Theory.Representation.BinaryOffender.CubicRatio.Monotonicity
import all CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.MiddleRecognition

/-!
# The strict TI bound used in the non-Mathieu family sieve

The original qrc module either lies in the outside parabolic two-core,
where the multiple-chief-factor and dual-FF arguments bound its quadratic
ratio by two, or escapes that core. In the latter case TI supplies the
strict Bender actor bound. The remaining symplectic opposite pair is
recognized over its actual coefficient field, and its strict actor bound
survives the full-core quotient lift. Faithful equivariant transport takes
that bound back to the unchanged qrc action.

This is the numerical implication of source 3.1.8(2) needed by 3.2.9.
The literal chosen-module application is in NonFFSourceNonMathieuFamilyComplete.
The internal import of MiddleRecognition is used only to eliminate its
non-exposed recognized-pair disjunction; no public boundary is changed.
Source: Aschbacher--Smith, printed pp.576,582--583, using E.2.7--15.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuFamily
open ChapterD ChapterD.UniqueFactor
open ChapterE ChapterE.Witnesses ChapterE.Witnesses.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
section Local
variable {H : Type*} [Group H] [Finite H]

private theorem marked_cubicRatio_lt_two
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (V U : Subgroup H) [IsElementaryAbelian 2 V]
    (hVT : V ≤ (T : Subgroup H)) (hvn : (V.subgroupOf T).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (w : MarkedModel T (ChapterB.minimalParabolicMax T hP) V) :
    cubicRatio (DihedralCubic.canonicalAction U V hU) < 2 := by
  let := DihedralCubic.centralizer_normal U V hU
  let := w.field
  let := w.finiteField
  let := w.charTwo
  have hTV : (T : Subgroup H) ≤ normalizer (V : Set H) :=
    (normal_subgroupOf_iff_le_normalizer hVT).mp hvn
  have hNV : normalizer (V : Set H) ≤ ChapterB.minimalParabolicMax T hP :=
    minimalParabolic_normalizer_le T hP V
      (IsElementaryAbelian.isPGroup 2 V) hTV hout
  have h := w.pair.hypotheses hVT hTV hVM hNV
  have hSU : (w.pair.sylow : Subgroup w.pair.subgroup).map
      w.pair.subgroup.subtype ≤ U :=
    w.pair.sylow_eq.le.trans (inf_le_left.trans hTU)
  have hproper : V.subgroupOf w.pair.subgroup ≠ ⊤ :=
    w.pair.proper_of_quotient_card_ne_one hNV (by
      rw [Nat.card_congr w.model.toEquiv]
      have hdiv : 2 ∣ Nat.card (Theory.SpecificGroups.SymplecticFour.Sp w.F) := by
        rw [Theory.SpecificGroups.SymplecticFour.card_sp, w.field_card]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
          ((dvd_pow_self 2 (Nat.ne_of_gt w.exponent_positive : w.exponent ≠ 0)).trans
            (dvd_pow_self _ (by decide : 4 ≠ 0))) _) _
      intro hone
      rw [hone] at hdiv
      norm_num at hdiv)
  let q : U →* (U ⧸ (centralizer (V : Set H)).subgroupOf U) :=
    QuotientGroup.mk' _
  have hh := DihedralCubic.ambient_cubic_actor_strict_symplectic_four_of_positive_exponent
    w.pair.le hU h hSU hproper (w.pair.fitting hTV hfit)
    w.exponent w.exponent_positive w.field_card w.model w.modelSylow
    w.center_placement q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
  exact hh.2.2.2.2.2

private theorem recognized_cubicRatio_lt_two
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (V U : Subgroup H) [IsElementaryAbelian 2 V]
    (hVT : V ≤ (T : Subgroup H)) (hvn : (V.subgroupOf T).Normal)
    (hVM : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H)
    (hTI : ∀ g ∈ ChapterB.minimalParabolicMax T hP,
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨ V.map (MulAut.conj g).toMonoidHom = V)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (hr : HasRecognizedPair
      (T.mapSurjective (QuotientGroup.mk'_surjective (ChapterB.minimalParabolicCore T hP)))
      ((ChapterB.minimalParabolicMax T hP).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)))
      (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)))) :
    cubicRatio (ChapterE.DihedralCubic.canonicalAction U V hU) < 2 := by
  rcases hr with hb | hs
  · obtain ⟨n,⟨w⟩⟩ := hb
    obtain ⟨w'⟩ := BenderPlacement.lift_original_witness T hP V hVT hvn hVM w
    exact BenderPlacement.original_witness_cubicRatio_lt_two hP hVT hvn hVM hout hfit hTI w' hTU hU
  · obtain ⟨w⟩ := hs
    obtain ⟨w'⟩ := MarkedModel.lift T hP V hVT hvn hVM w
    exact marked_cubicRatio_lt_two T hP V U hVT hvn hVM hout hfit hTU hU w'

end Local

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}
open Chapter3

omit [Finite G] in
private theorem intrinsic_cubicRatio_lt_two
    (h : QrcHypotheses T M M₀ H V)  :
    letI := h.module_elementary
    letI : IsElementaryAbelian 2 (V.subgroupOf H) :=
      IsElementaryAbelian.subgroupOf (h.module_le_sylow.trans h.right_mem.1.1.2)
    cubicRatio (ChapterE.DihedralCubic.canonicalAction
      ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H)
      (V.subgroupOf H) h.intrinsic_module_normalized) < 2 →
      cubicRatio (imageRepresentation M₀ V h.module_normalized) < 2 := by
  let := h.module_elementary
  let S := T.subtype h.right_mem.1.1.2
  let W := V.subgroupOf H
  have hVH : V ≤ H := h.module_le_sylow.trans h.right_mem.1.1.2
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVH
  let hTV := h.intrinsic_module_normalized
  let σ := imageRepresentation M₀ V h.module_normalized
  intro hbound
  let := ChapterE.DihedralCubic.centralizer_normal (S : Subgroup H) W hTV
  let ρ := ChapterE.DihedralCubic.canonicalAction (S : Subgroup H) W hTV
  let q := ChapterE.DihedralCubic.projection (S : Subgroup H) W hTV
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  let i : (S : Subgroup H) →* M₀ :=
    (H.subtype.comp (S : Subgroup H).subtype).codRestrict M₀ (fun s => h.sylow_le s.property)
  let f := (actionHom M₀ V h.module_normalized).rangeRestrict.comp i
  have hk : q.ker ≤ f.ker := by
    intro s hs
    have hsC : s ∈ (centralizer (W : Set H)).subgroupOf (S : Subgroup H) :=
      (QuotientGroup.eq_one_iff s).mp hs
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    have hc := congrArg H.subtype (hsC ⟨v,hVH v.property⟩ v.property)
    change (v : G) * (s.val : G) = (s.val : G) * (v : G) at hc
    change (s.val : G) * (v : G) * (s.val : G)⁻¹ = v
    rw [←hc,mul_inv_cancel_right]
  let ψ := q.liftOfSurjective hqs ⟨f,hk⟩
  have hψ (s : (S : Subgroup H)) : ψ (q s) = f s := q.liftOfRightInverse_comp_apply _ _ _ s
  let e := subgroupOfEquivOfLe hVH
  let E : Additive W ≃ₗ[ZMod 2] Additive V :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
  have he : ∀ a v, E (ρ a v) = σ (ψ a) (E v) := by
    intro a v
    obtain ⟨s,rfl⟩ := hqs a
    rw [hψ]
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg H.subtype
      (ChapterE.DihedralCubic.representation_apply (S : Subgroup H) W hTV q hqs
        (QuotientGroup.ker_mk' _) s v)
  have hψi : Function.Injective ψ := by
    intro a b hab
    apply ChapterE.DihedralCubic.representation_injective (S : Subgroup H) W hTV q hqs
      (QuotientGroup.ker_mk' _)
    apply LinearMap.ext
    intro v
    apply E.injective
    change E (ρ a v) = E (ρ b v)
    exact (he a v).trans ((congrArg (fun z => σ z (E v)) hab).trans (he b v).symm)
  exact (cubicRatio_le_of_injective_equivariant ρ σ ψ hψi E he).trans_lt hbound

private theorem outsideCore_cubicRatio_lt_two
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hout : ¬ V ≤ H.pCoreIn 2)
    (hTI : ∀ g ∈ M, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V) :
    letI := h.module_elementary
    cubicRatio (imageRepresentation M₀ V h.module_normalized) < 2 := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := h.module_elementary
  let σ := imageRepresentation M₀ V h.module_normalized
  by_cases hff : IsFFModule σ
  · exact ((isFFModule_iff_cubicRatio_le_one σ).mp hff).trans_lt (by norm_num)
  have hVT : V ≤ (T : Subgroup G) := d.module_le_core.trans (left_core_le_sylow d)
  have hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) := by
    by_contra hj
    exact hff (internalActionImage_isFFModule_of_thompson_not_le T M₀ V h.sylow_le
      hVT h.module_normalized hj)
  let S := T.subtype h.right_mem.1.1.2
  let W := V.subgroupOf H
  have hVH : V ≤ H := hVT.trans h.right_mem.1.1.2
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVH
  let hp := h.intrinsic_minimalParabolic hM hu hJ
  have hWS : W ≤ (S : Subgroup H) := fun _ hx => hVT hx
  have hTV : (S : Subgroup H) ≤ normalizer (W : Set H) := by
    rw [←subgroupOf_normalizer_eq hVH]
    exact fun _ hx => h.module_normalized (h.sylow_le hx)
  have hvn : (W.subgroupOf (S : Subgroup H)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hWS).mpr hTV
  have hWcore : W ≤ (ChapterB.minimalParabolicMax S hp).pCoreIn 2 :=
    h.intrinsic_module_le_maximal_core hG hM hp
  have hWout : ¬ W ≤ ChapterB.minimalParabolicCore S hp := by
    intro he
    have hc : W ≤ pCore 2 H := by
      rw [←ChapterB.minimalParabolic_sylow_inf_core S hp]
      exact le_inf hWS he
    apply hout
    have hm := map_mono (f := H.subtype) hc
    change (V.subgroupOf H).map H.subtype ≤ H.pCoreIn 2 at hm
    simpa only [map_subgroupOf_eq_of_le hVH] using hm
  have hfit : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp
        (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) h.right_mem.1.1))
  have hWTI : ∀ g ∈ ChapterB.minimalParabolicMax S hp,
      W ⊓ W.map (MulAut.conj g).toMonoidHom = ⊥ ∨ W.map (MulAut.conj g).toMonoidHom = W := by
    rw [h.intrinsic_maximal_eq_intersection hp]
    intro g hg
    exact BenderPlacement.restrict_TI hVH hTI g hg.2
  apply intrinsic_cubicRatio_lt_two h
  rcases ChapterE.Witnesses.source_cubicRatio_lt_two_or_nonbinary_symplectic
    (sqtk_of_mem_H hG h.right_mem.1.1.1) S hp W S hWS hvn hWcore hWout hfit hWTI le_rfl hTV with
      hbound | ⟨K,hK,hN,hgen,f,hf,hm⟩
  · exact hbound
  let := hN
  by_cases hsmall : Nat.card (W.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hp))) = 2
  · obtain ⟨w⟩ := Involution.source_star_order_two S hp W hWS hvn hWcore hsmall
    exact BenderPlacement.original_witness_cubicRatio_lt_two hp hWS hvn hWcore hWout hfit hWTI
      (BenderPlacement.OriginalWitness.of_dihedral (n := 1) w) le_rfl hTV
  have hne : W.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hp)) ≠ ⊥ := by
    intro he
    exact hWout (by simpa only [QuotientGroup.ker_mk'] using (map_eq_bot_iff W).mp he)
  have hsize : 2 < Nat.card (W.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hp))) := by
    have hc := (one_lt_card_iff_ne_bot _).mpr hne
    omega
  obtain ⟨F,hF,hfin,hFcard,⟨e⟩⟩ := hm
  let : CharP F 2 := EvenProjective.charTwo_of_card hFcard
  let J := ChapterB.minimalParabolicCore S hp
  let B := ChapterB.minimalParabolicMax S hp
  let q := QuotientGroup.mk' J
  let Sq := S.mapSurjective (QuotientGroup.mk'_surjective J)
  let Wq := W.map q
  let Kq := K.map q
  have hVH : V ≤ H := h.module_le_sylow.trans h.right_mem.1.1.2
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVH
  let : IsElementaryAbelian 2 Wq := IsElementaryAbelian.map q
  have hWS : W ≤ (S : Subgroup H) := fun _ hx => h.module_le_sylow hx
  have hWqS : Wq ≤ (Sq : Subgroup (H ⧸ J)) := map_mono hWS
  have hTV : (S : Subgroup H) ≤ normalizer (W : Set H) := h.intrinsic_module_normalized
  have hTqW : (Sq : Subgroup (H ⧸ J)) ≤ normalizer (Wq : Set (H ⧸ J)) :=
    (map_mono hTV).trans (le_normalizer_map q)
  have hWcore : W ≤ B.pCoreIn 2 := h.intrinsic_module_le_maximal_core hG hM hp
  have hs : ¬ Group.IsSolvable H := by
    intro hsol
    let := hsol
    exact hK.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective K.subtype_injective)
  obtain ⟨hKs,_,hKn,hKT⟩ := ChapterE.Structure.source_normal_simple_image S hp hs K hK hgen
  let : IsSimpleGroup Kq := hKs
  let : Kq.Normal := hKn
  have hmin : ChapterB.IsMinimalParabolicOver Sq ⊤ :=
    (ChapterE.Structure.source_star_minimal_core_free S hp).1
  have hcore : ChapterB.minimalParabolicCore Sq hmin = ⊥ :=
    (ChapterE.Structure.source_star_minimal_core_free S hp).2
  have hmax : ChapterB.minimalParabolicMax Sq hmin = B.map q :=
    (ChapterB.minimalParabolicMax_map_core S hp q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  have hWqcore : Wq ≤ (ChapterB.minimalParabolicMax Sq hmin).pCoreIn 2 := by
    rw [hmax]
    exact (map_mono hWcore).trans
      (Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_image_le q B)
  let e₀ : Kq ≃* Sp F := e.trans EvenProjective.equiv.symm
  obtain ⟨c,hmark⟩ := ChapterE.Structure.SymplecticFour.exists_alignment hFcard
    (by omega : 1 ≤ f) Sq Kq e₀
  let e₁ : Sp F ≃* Kq := (e₀.trans (MulAut.conj c)).symm
  have hsq : IsSQTK KnownSimple.IsKnownSimple (H ⧸ J) :=
    ChapterE.Structure.source_star_sqtk ChapterA.Section02.theoremA_knownSimple
      (sqtk_of_mem_H hG h.right_mem.1.1.1) S hp hs
  have hrec := ChapterE.Structure.SymplecticFour.source_hasRecognizedPair
    hFcard (by omega : 1 < f) hsq Sq hmin hcore Kq e₁ hmark hKT
    Wq hWqS hWqcore hTqW hsize
  rw [hmax] at hrec
  exact recognized_cubicRatio_lt_two S hp W S hWS hvn hWcore hWout hfit hWTI le_rfl hTV hrec

/-- Source 3.1.8(2) on a TI qrc module, with the dual-FF branch discharged. -/
theorem quadratic_le_two_or_cubic_lt_two
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hne : V ≠ ⊥)
    (hTI : ∀ g ∈ M, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V) :
    letI := h.module_elementary
    quadraticRatio (imageRepresentation M₀ V h.module_normalized) ≤ 2 ∨
      cubicRatio (imageRepresentation M₀ V h.module_normalized) < 2 := by
  let := h.module_elementary
  by_cases hcore : V ≤ H.pCoreIn 2
  · left
    rcases h.quadraticRatio_le_two_or_dualFF hG hM hu hne hcore with hb | hd
    · exact hb
    · exact h.quadraticRatio_le_two_of_dualFF hG hM hd
  · exact Or.inr (outsideCore_cubicRatio_lt_two h hG hM hu hcore hTI)

end CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuFamily
