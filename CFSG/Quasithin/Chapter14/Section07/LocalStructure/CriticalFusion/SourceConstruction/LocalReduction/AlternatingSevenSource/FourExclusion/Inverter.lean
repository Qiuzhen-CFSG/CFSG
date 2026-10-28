module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryBorelKernel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPlaneCubic

/-!
# The original partial inverter in the four-dimensional branch of 14.7.50

The marked point parabolic constructs an element of the original T ∩ L
inverting L₁/O₂(L₁), using earlier structural results only at the original
G,T. The same element fixes the intrinsic two-core quotient of the residual
of the literal centralizer kernel on each local intersection.

Source: Aschbacher–Smith 14.7.50, printed p.1064, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Chapter12.Section08 CriticalFusion.Source
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open BinaryLinear.OuterCyclic
open Chapter13.Section08.Components Swapped Swapped.LinearTwo
open Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
  (coreAction coreAction_eq_one_iff)
universe u
section Model
variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)
private noncomputable def modelMap (e : (L ⧸ pCore 2 L) ≃* SL) : L →* SL :=
  e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

private noncomputable def modelAction (e : (L ⧸ pCore 2 L) ≃* SL) :
    normalizer (L : Set G) →* MulAut SL :=
  (MulAut.congr e).toMonoidHom.comp ((quotientAut (pCore 2 L)).comp L.normalizerMonoidHom)

omit [Finite G] in
private theorem modelAction_apply (e : (L ⧸ pCore 2 L) ≃* SL)
    (g : normalizer (L : Set G)) (l : L) :
    modelAction L e g (modelMap L e l) = modelMap L e (L.normalizerMonoidHom g l) := by
  change e (quotientAut (pCore 2 L) (L.normalizerMonoidHom g)
    (e.symm (e (QuotientGroup.mk' (pCore 2 L) l)))) = _
  rw [e.symm_apply_apply, quotientAut_apply_mk]
  rfl

omit [Finite G] in
private theorem modelAction_inner (e : (L ⧸ pCore 2 L) ≃* SL) (l : L) :
    modelAction L e ⟨l,L.le_normalizer l.property⟩ = MulAut.conj (modelMap L e l) := by
  apply MulEquiv.ext
  intro y
  obtain ⟨a,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) y
  change modelAction L e ⟨l,L.le_normalizer l.property⟩ (modelMap L e a) =
    MulAut.conj (modelMap L e l) (modelMap L e a)
  rw [modelAction_apply]
  change modelMap L e (l * a * l⁻¹) = modelMap L e l * modelMap L e a * (modelMap L e l)⁻¹
  rw [map_mul,map_mul,map_inv]

omit [Finite G] in
private theorem modelAction_image (e : (L ⧸ pCore 2 L) ≃* SL)
    (A : Subgroup G) (hAL : A ≤ L) :
    (A.subgroupOf (normalizer (L : Set G))).map (modelAction L e) =
      ((A.subgroupOf L).map (modelMap L e)).map MulAut.conj := by
  ext α
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨modelMap L e ⟨a,hAL ha⟩, ⟨⟨a,hAL ha⟩,ha,rfl⟩, ?_⟩
    exact (modelAction_inner L e ⟨a,hAL ha⟩).symm
  · rintro ⟨_,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨⟨a,L.le_normalizer a.property⟩,ha,modelAction_inner L e a⟩

omit [Finite G] in
private theorem modelAction_preserves (e : (L ⧸ pCore 2 L) ≃* SL)
    (A : Subgroup G) (g : normalizer (L : Set G))
    (hA : (g : G) ∈ normalizer (A : Set G)) :
    ((A.subgroupOf L).map (modelMap L e)).map (modelAction L e g).toMonoidHom =
      (A.subgroupOf L).map (modelMap L e) := by
  have hle : ((A.subgroupOf L).map (modelMap L e)).map
      (modelAction L e g).toMonoidHom ≤ (A.subgroupOf L).map (modelMap L e) := by
    rintro _ ⟨_,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨L.normalizerMonoidHom g a, (mem_normalizer_iff.mp hA a).mp ha,
      (modelAction_apply L e g a).symm⟩
  apply eq_of_le_of_card_ge hle
  exact le_of_eq (card_map_of_injective (modelAction L e g).injective).symm

end Model
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem exists_L_sylow (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : CFSG.Quasithin.Chapter12.Section02.Structural1222At CFSG.KnownSimple.IsKnownSimple T) :
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup G).subgroupOf L := by
  obtain ⟨S,hS⟩ := (T.subtype (le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G))).exists_map_subtype_eq_inf_of_normalizes
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer (h.sylow_normalizes_at structural))
  refine ⟨S, map_injective L.subtype_injective ?_⟩
  rw [hS,Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right,subgroupOf_map_subtype]

private theorem point_residual_marking (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : CFSG.Quasithin.Chapter12.Section02.Structural1222At CFSG.KnownSimple.IsKnownSimple T) :
    ∃ (e : (L ⧸ pCore 2 L) ≃* SL) (P : Subgroup SL),
        (P = pointParabolicSL ∨ P = lineParabolicSL) ∧
        ((F.Li L 1).subgroupOf L).map (modelMap L e) = residual P ∧
        ((T : Subgroup G).subgroupOf L).map (modelMap L e) = borelSL := by
  let := h.chosen.elementary
  let e₀ := h.naturalMarking.quotientEquiv.trans (slEquivLinear 3).symm
  let f := modelMap L e₀
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = pCore 2 L :=
      (MonoidHom.ker_comp_of_injective _ _ e₀.injective).trans (QuotientGroup.ker_mk' _)
    rw [he]
    exact pCore_isPGroup
  let A₀ := (F.Li L 1).subgroupOf L
  let A := A₀.map f
  have hAL : F.Li L 1 ≤ L := (F.Li_le L 1).trans inf_le_left
  have hp₀ : IsPPerfect 2 A₀ := (show IsPPerfect 2 (F.Li L 1) from isPPerfect_embedded_pResidual 2 _).of_surjective
    (subgroupOfEquivOfLe hAL).symm.toMonoidHom (subgroupOfEquivOfLe hAL).symm.surjective
  have hp : IsPPerfect 2 A := hp₀.of_surjective (f.subgroupMap A₀) (f.subgroupMap_surjective A₀)
  have hqker : IsPGroup 2 (f.subgroupMap A₀).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let eA := subgroupOfEquivOfLe hAL
  let eQ := QuotientGroup.congr (pCore 2 A₀) (pCore 2 (F.Li L 1)) eA (pCore_map_iso 2 eA)
  let eImage := MonoidHom.quotientPCoreEquivOfSurjective (f.subgroupMap A₀)
    (f.subgroupMap_surjective A₀) hqker
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 :=
    (Nat.card_congr eImage.toEquiv).symm.trans
      ((Nat.card_congr eQ.toEquiv).trans (pointResidual_core_quotient_card_at h structural))
  obtain ⟨S,hS⟩ := exists_L_sylow h structural
  let R := S.mapSurjective (f := f) (e₀.surjective.comp (QuotientGroup.mk'_surjective _))
  have hn₀ : (S : Subgroup L) ≤ normalizer (A₀ : Set L) := by
    rw [hS]
    intro x hx
    apply mem_normalizer_iff.mpr
    intro a
    exact (mem_normalizer_iff.mp (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes_at structural) hx) a)
  have hn : (R : Subgroup SL) ≤ normalizer (A : Set SL) :=
    (map_mono hn₀).trans (le_normalizer_map f)
  obtain ⟨_,_,_,_,g,P,hP,_,hmark,hborel,_⟩ := ResidualRecognition.recognize A R hp hc hn
  refine ⟨e₀.trans (MulAut.conj g),P,hP,?_⟩
  constructor
  · change A₀.map ((MulAut.conj g).toMonoidHom.comp f) = residual P
    rw [← map_map]
    exact hmark
  · change ((T : Subgroup G).subgroupOf L).map
      ((MulAut.conj g).toMonoidHom.comp f) = borelSL
    rw [← map_map,← hS]
    exact hborel


/-- The actual two-perfect Borel is supplemented by the residual of its
literal quotient-action kernel and the original point group. -/
theorem point_borel_kernel_supplement_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (B : Subgroup G) (hBM : B ≤ normalizer (L : Set G))
    (hB : IsPPerfect 2 B) (hAB : F.Li L 1 ≤ B)
    (hBA : B ≤ normalizer (F.Li L 1 : Set G)) :
    F.Li L 1 ⊔ binaryBorelCentralResidual L B hBM = B := by
  let A := F.Li L 1
  let M := normalizer (L : Set G)
  let A₀ := A.subgroupOf B
  let f := binaryBorelAction L B hBM
  have hAL : A ≤ L := (F.Li_le L 1).trans inf_le_left
  let : A₀.Normal := normal_subgroupOf_of_le_normalizer hBA
  have hpA : IsPPerfect 2 A₀ :=
    (show IsPPerfect 2 A from isPPerfect_embedded_pResidual 2 _).of_surjective
      (subgroupOfEquivOfLe hAB).symm.toMonoidHom (subgroupOfEquivOfLe hAB).symm.surjective
  obtain ⟨e,P,hP,hm,hs⟩ := point_residual_marking (F := F) h structural
  let a := modelAction L e
  let g : B →* MulAut SL := a.comp (inclusion hBM)
  let X := g.range
  let R := (residual P).map MulAut.conj
  have hAim : A₀.map g = R := by
    change (A.subgroupOf B).map (a.comp (inclusion hBM)) = R
    rw [←map_map]
    have he : (A.subgroupOf B).map (inclusion hBM) = A.subgroupOf M := by
      apply map_injective M.subtype_injective
      rw [map_map, show M.subtype.comp (inclusion hBM) = B.subtype from rfl,
        map_subgroupOf_eq_of_le hAB,map_subgroupOf_eq_of_le (hAB.trans hBM)]
    rw [he]
    exact (modelAction_image L e A hAL).trans (congrArg (map MulAut.conj) hm)
  have hXP : X ≤ P.map MulAut.conj := by
    rintro _ ⟨x,rfl⟩
    have hh := modelAction_preserves L e A (inclusion hBM x) (hBA x.property)
    rw [hm] at hh
    obtain ⟨y,hy,he⟩ := preserving_residual_is_conj P hP (g x) hh
    exact ⟨y,hy,he.symm⟩
  have hpX := hB.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  have hXA : X ≤ R := by
    let Q := P.map MulAut.conj
    have hpXQ := hpX.of_surjective (subgroupOfEquivOfLe hXP).symm.toMonoidHom
      (subgroupOfEquivOfLe hXP).symm.surjective
    have hh := map_mono (f := Q.subtype)
      (le_pResidual_of_isPPerfect (X.subgroupOf Q) hpXQ)
    rw [map_subgroupOf_eq_of_le hXP] at hh
    exact hh.trans_eq (map_embedded_pResidual 2 P MulAut.conj).symm
  have him : A₀.map g = g.range :=
    hAim.trans (le_antisymm (hAim ▸ map_le_range g A₀) hXA)
  have himf : A₀.map f = f.range := by
    apply map_injective (f := (MulAut.congr e).toMonoidHom) (MulAut.congr e).injective
    rw [map_map, ←MonoidHom.range_comp]
    exact him
  have he := congrArg (map B.subtype)
    (sup_embedded_pResidual_kernel_eq_top 2 A₀ hB hpA f himf)
  change (A₀ ⊔ (pResidual 2 f.ker).map f.ker.subtype).map B.subtype = _ at he
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hAB,
    ←MonoidHom.range_eq_map, range_subtype] at he
  exact he

/-- The actual Sylow intersection T∩L contains an inverter of the original
point cubic. Its existence follows from the marked parabolic commutator,
not from an additional local-action premise. -/
theorem exists_point_core_inverter_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
      ∀ x : F.Li L 1 ⧸ pCore 2 (F.Li L 1),
        coreAction (F.Li L 1)
          ⟨t,ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes_at structural) t.property.1⟩ x = x⁻¹ := by
  let A := F.Li L 1
  let S := (T : Subgroup G) ⊓ L
  have hn : S ≤ normalizer (A : Set G) :=
    inf_le_left.trans (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes_at structural))
  have hne : ∃ t : S, coreAction A ⟨t,hn t.property⟩ ≠ 1 := by
    by_contra! hall
    have hc : ⁅A,S⁆ ≤ A.pCoreIn 2 :=
      commutator_le_of_normalizerQuotientAction_eq_one A S (pCore 2 A) hn hall
    have hp : IsPGroup 2 (⁅A,S⁆ : Subgroup G) := (isPGroup_pCoreIn 2 A).to_le hc
    have hAL : A ≤ L := (F.Li_le L 1).trans inf_le_left
    have hSL : S ≤ L := inf_le_right
    obtain ⟨e,P,hP,hm,hs⟩ := point_residual_marking (F := F) h structural
    let q := modelMap L e
    have hS : (S.subgroupOf L).map q = borelSL := by
      have heS : S.subgroupOf L = (T : Subgroup G).subgroupOf L := by
        ext x
        exact and_iff_left x.property
      rw [heS]
      exact hs
    have hmodel : ⁅residual P,borelSL⁆ = residual P := by
      let B₂ : Sylow 2 SL := Sylow.ofCard borelSL (by rw [card_borelSL,card_SL]; decide +kernel)
      have hcard : Nat.card (residual P ⧸ pCore 2 (residual P)) = 3 := by
        rcases hP with rfl | rfl
        · rw [MarkedAutomorphisms.point_residual]
          exact card_point_core_quotient
        · rw [MarkedAutomorphisms.line_residual]
          exact card_line_core_quotient
      have hBP : borelSL ≤ P := by
        rcases hP with rfl | rfl
        · exact inf_le_left
        · exact inf_le_right
      exact ResidualRecognition.commutator_sylow_eq (residual P) B₂
        (isPPerfect_embedded_pResidual 2 P) hcard
        ((hBP.trans P.le_normalizer).trans
          (normalizer_le_normalizer_characteristic_image P (pResidual 2 P)))
    have heC : ⁅A.subgroupOf L,S.subgroupOf L⁆ = (⁅A,S⁆).subgroupOf L := by
      apply map_injective L.subtype_injective
      rw [map_commutator,map_subgroupOf_eq_of_le hAL,map_subgroupOf_eq_of_le hSL,
        map_subgroupOf_eq_of_le ((hc.trans (pCoreIn_le 2 A)).trans hAL)]
    have hpg : IsPGroup 2 (residual P) := by
      have hh := (hp.comap_subtype (K := L)).map q
      rw [comap_subtype,←heC,map_commutator,hm,hS,hmodel] at hh
      exact hh
    have hc12 : Nat.card (residual P) = 12 := by
      rcases hP with rfl | rfl
      · exact card_point_residual
      · exact card_line_residual
    obtain ⟨m,hm⟩ := hpg.exists_card_eq
    have hdiv : 3 ∣ 2 ^ m := by rw [←hm,hc12]; decide
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hdiv)
  obtain ⟨t,ht⟩ := hne
  exact ⟨t,(Theory.GroupTheory.CubicAutomorphismLines.automorphism_eq_one_or_inv
    (pointResidual_core_quotient_card_at (F := F) h structural) _).resolve_left ht⟩


omit [Finite G] in
/-- The local intersection normalizes the actual point residual because it
normalizes both L and its point normalizer. -/
theorem local_intersection_normalizes_point
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    I ⊓ normalizer (L : Set G) ≤ normalizer (F.Li L 1 : Set G) := by
  have hn : I ⊓ normalizer (L : Set G) ≤ normalizer ((L ⊓ F.H : Subgroup G) : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans (hI.2.1.trans F.H.le_normalizer))).trans
      inf_normalizer_le_normalizer_inf
  change I ⊓ normalizer (L : Set G) ≤
    normalizer (((pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype : Subgroup G) : Set G)
  exact hn.trans (normalizer_le_normalizer_characteristic_image (L ⊓ F.H)
    (pResidual 2 (L ⊓ F.H : Subgroup G)))

/-- The original source supplies the partial inverter and its full supplement
on every local intersection. Both actions concern intrinsic two-core quotients;
the residual complement is the actual quotient-action kernel, with no split
extension or extra local-action premise. -/
theorem local_partial_inverter_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    let J := I ⊓ normalizer (L : Set G)
    let B := (pResidual 2 J).map J.subtype
    let hBM : B ≤ normalizer (L : Set G) := (map_subtype_le _).trans inf_le_right
    let D := binaryBorelCentralResidual L B hBM
    F.Li L 1 ⊔ D = B ∧
      Nat.card ((F.Li L 1) ⧸ pCore 2 (F.Li L 1)) = 3 ∧
      J ≤ normalizer (F.Li L 1 : Set G) ∧
      ∃ (t : ((T : Subgroup G) ⊓ L : Subgroup G))
        (htJ : (t : G) ∈ J)
        (_htB : (t : G) ∈ normalizer (B : Set G))
        (htD : (t : G) ∈ normalizer (D : Set G)),
        (∀ x : F.Li L 1 ⧸ pCore 2 (F.Li L 1),
          coreAction (F.Li L 1)
            ⟨t,local_intersection_normalizes_point I hI htJ⟩ x = x⁻¹) ∧
        coreAction D ⟨t,htD⟩ = 1 := by
  let A := F.Li L 1
  let J := I ⊓ normalizer (L : Set G)
  let B := (pResidual 2 J).map J.subtype
  have hBM : B ≤ normalizer (L : Set G) := (map_subtype_le _).trans inf_le_right
  let D := binaryBorelCentralResidual L B hBM
  have hAJ : A ≤ J := le_inf (F.Li_one_le_of_mem_Hz hI)
    (((F.Li_le L 1).trans inf_le_left).trans L.le_normalizer)
  have hJA : J ≤ normalizer (A : Set G) := local_intersection_normalizes_point I hI
  have hpA : IsPPerfect 2 A := isPPerfect_embedded_pResidual 2 _
  have hAB : A ≤ B := by
    have hh := embedded_pResidual_mono 2 hAJ
    simpa only [(pResidual_eq_top_iff 2 A).mpr hpA,
      ←MonoidHom.range_eq_map,range_subtype] using hh
  have hgen : A ⊔ D = B := point_borel_kernel_supplement_at h structural B hBM
    (isPPerfect_embedded_pResidual 2 J) hAB ((map_subtype_le _).trans hJA)
  refine ⟨hgen,pointResidual_core_quotient_card_at h structural,hJA,?_⟩
  obtain ⟨t,hti⟩ := exists_point_core_inverter_at (F := F) h structural
  have htJ : (t : G) ∈ J :=
    ⟨F.sylow_le_of_mem_Hz hI t.property.1,L.le_normalizer t.property.2⟩
  have htB : (t : G) ∈ normalizer (B : Set G) :=
    normalizer_le_normalizer_characteristic_image J (pResidual 2 J)
      (J.le_normalizer htJ)
  have htD : (t : G) ∈ normalizer (D : Set G) :=
    binaryBorelCentralResidual_normalized L B hBM ⟨htB,L.le_normalizer t.property.2⟩
  exact ⟨t,htJ,htB,htD,hti,binaryBorelCentralResidual_fixed L B hBM t.property.2 htB⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
