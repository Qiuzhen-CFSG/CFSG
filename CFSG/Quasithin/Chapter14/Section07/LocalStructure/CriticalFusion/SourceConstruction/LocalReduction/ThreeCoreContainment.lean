module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCoreIntersection
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms
public import Theory.SpecificGroups.PSL3Two.Parabolics.ResidualCommutator
public import Theory.GroupTheory.PResidual.NormalizedImageContainment
public import Theory.SpecificGroups.PSL3Two.Parabolics.NormalAction

/-!
# Point containment in the actual normal three-lift

Let Y be normal in an original local J and suppose Y/O₂(Y) is a three-group
and O₂(Y) < Y ∩ N_G(L). The two-residual of this intersection has a nontrivial
literal action on L/O₂(L). The original natural marking identifies its
image with the inner A₄ of the point parabolic. Commutators with T ∩ L recover
that same image inside Y ∩ L. Two-perfectness then lifts the containment
through O₂(L), which normalizes Y, proving L₁ ≤ Y.

The private marking and quotient-action transports refine the established
argument in ExtraspecialNormalizerEquality, retaining the Sylow mark as well.
No Data, point normality, or local recognition premise is used. This proves
assertion (!!) of 14.5.20 in the original three-lift situation; the remaining
solvable exclusions and residual classification are separate obligations.

Source: Aschbacher–Smith, 14.5.20, printed p.1019; 14.7.9 and 14.7.27,
printed pp.1045,1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open BinaryLinear.OuterCyclic
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
    (structural : CFSG.Quasithin.Chapter12.Section02.Structural1222 CFSG.KnownSimple.IsKnownSimple.{u}) :
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup G).subgroupOf L := by
  obtain ⟨S,hS⟩ := (T.subtype (le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G))).exists_map_subtype_eq_inf_of_normalizes
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer (h.sylow_normalizes structural))
  refine ⟨S, map_injective L.subtype_injective ?_⟩
  rw [hS,Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right,subgroupOf_map_subtype]

private theorem point_residual_marking (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : CFSG.Quasithin.Chapter12.Section02.Structural1222 CFSG.KnownSimple.IsKnownSimple.{u}) :
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
      ((Nat.card_congr eQ.toEquiv).trans (pointResidual_core_quotient_card h structural))
  obtain ⟨S,hS⟩ := exists_L_sylow h structural
  let R := S.mapSurjective (f := f) (e₀.surjective.comp (QuotientGroup.mk'_surjective _))
  have hn₀ : (S : Subgroup L) ≤ normalizer (A₀ : Set L) := by
    rw [hS]
    intro x hx
    apply mem_normalizer_iff.mpr
    intro a
    exact (mem_normalizer_iff.mp (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes structural) hx) a)
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


/-- A strict normalizer intersection in a normal three-lift forces the
original point residual into that lift. -/
theorem local_three_lift_contains_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (Y : Subgroup J) [Y.Normal]
    (h3 : IsPGroup 3 (Y ⧸ pCore 2 Y))
    (hi : (Y.map J.subtype).pCoreIn 2 < Y.map J.subtype ⊓ normalizer (L : Set G)) :
    (F.Li L 1).subgroupOf J ≤ Y := by
  let M := normalizer (L : Set G)
  let A := F.Li L 1
  let B := Y.map J.subtype
  let I := B ⊓ M
  let R := (pResidual 2 I).map I.subtype
  let S := (T : Subgroup G) ⊓ L
  have hAL : A ≤ L := (F.Li_le L 1).trans inf_le_left
  have hAM : A ≤ M := hAL.trans L.le_normalizer
  have hAJ : A ≤ J := F.Li_one_le_of_mem_Hz hJ
  have hTJ : (T : Subgroup G) ≤ J := F.sylow_le_of_mem_Hz hJ
  have hTM : (T : Subgroup G) ≤ M := h.sylow_normalizes structural
  have hRM : R ≤ M := (map_subtype_le _).trans inf_le_right
  have hRB : R ≤ B := (map_subtype_le _).trans inf_le_left
  have hRH : R ≤ F.H := hRB.trans ((map_subtype_le Y).trans hJ.2.1)
  have hJY : J ≤ normalizer (B : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      Y.le_normalizer_map J.subtype
  have hNR : J ⊓ M ≤ normalizer (R : Set G) :=
    ((le_inf (inf_le_left.trans hJY) (inf_le_right.trans M.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf).trans
        (normalizer_le_normalizer_characteristic_image I (pResidual 2 I))
  have hRA : R ≤ normalizer (A : Set G) := by
    have hh := ((le_inf hRM (hRH.trans F.H.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf).trans
        (normalizer_le_normalizer_characteristic_image (L ⊓ F.H)
          (pResidual 2 (L ⊓ F.H : Subgroup G)))
    have he : A = (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype := by
      simp only [A,InvariantFlag.Li,show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide,if_false]
      rfl
    rw [he]
    exact hh
  obtain ⟨e,P,hP,hm,hs⟩ := point_residual_marking (F := F) h structural
  let q := modelMap L e
  let f := modelAction L e
  let R₀ := R.subgroupOf M
  let A₀ := A.subgroupOf M
  let S₀ := S.subgroupOf M
  let X := R₀.map f
  have hpR : IsPPerfect 2 R₀ := (isPPerfect_embedded_pResidual 2 I).of_surjective
    (subgroupOfEquivOfLe hRM).symm.toMonoidHom (subgroupOfEquivOfLe hRM).symm.surjective
  have hpX : IsPPerfect 2 X := hpR.of_surjective (f.subgroupMap R₀)
    (f.subgroupMap_surjective R₀)
  have hXne : X ≠ ⊥ := by
    intro hz
    obtain ⟨x,hx⟩ := local_three_intersection_quotient_action h structural J hJ Y h3 hi
    have hh : f (inclusion hRM x) = 1 := mem_bot.mp (hz ▸
      mem_map_of_mem f (show inclusion hRM x ∈ R₀ from x.property))
    apply hx
    apply (MulAut.congr e).injective
    exact hh.trans (map_one (MulAut.congr e)).symm
  have hXP : X ≤ P.map MulAut.conj := by
    rintro _ ⟨x,hx,rfl⟩
    have hh := modelAction_preserves L e A x (hRA hx)
    change ((A.subgroupOf L).map q).map (f x).toMonoidHom = _ at hh
    rw [hm] at hh
    obtain ⟨g,hg,he⟩ := preserving_residual_is_conj P hP (f x) hh
    exact ⟨g,hg,he.symm⟩
  have hAim : A₀.map f = (residual P).map MulAut.conj := by
    rw [modelAction_image L e A hAL,hm]
  have hn₀ : A₀ ≤ normalizer (R₀ : Set M) := by
    rw [←subgroupOf_normalizer_eq hRM]
    intro x hx
    exact hNR ⟨hAJ hx,hAM hx⟩
  have hXeq : X = (residual P).map MulAut.conj :=
    twoPerfect_normalized_parabolic_image P hP X hpX hXne hXP
      (hAim ▸ (map_mono hn₀).trans (le_normalizer_map f))
  have hSL : S ≤ L := inf_le_right
  have hSM : S ≤ M := hSL.trans L.le_normalizer
  have hSim : S₀.map f = borelSL.map MulAut.conj := by
    rw [modelAction_image L e S hSL]
    have hS : S.subgroupOf L = (T : Subgroup G).subgroupOf L := by
      ext x
      exact and_iff_left x.property
    rw [hS,hs]
  have hc : ⁅residual P,borelSL⁆ = residual P := by
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
  have hcomm : (⁅R₀,S₀⁆).map f = A₀.map f := by
    rw [map_commutator]
    change ⁅X,S₀.map f⁆ = A₀.map f
    rw [hXeq,hSim,←map_commutator,hc,hAim]
  let C₀ := ⁅R₀,S₀⁆
  let C := C₀.map M.subtype
  have hC : C = ⁅R,S⁆ := by
    change (⁅R.subgroupOf M,S.subgroupOf M⁆).map M.subtype = _
    rw [map_commutator,map_subgroupOf_eq_of_le hRM,map_subgroupOf_eq_of_le hSM]
  have hCL : C ≤ L := by
    rw [hC]
    exact (commutator_mono le_rfl hSL).trans
      (le_normalizer_iff_commutator_le_right.mp hRM)
  have hCB : C ≤ B := by
    rw [hC]
    exact (commutator_mono hRB le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp ((inf_le_left : S ≤ (T : Subgroup G)).trans
        (hTJ.trans hJY)))
  have hCim : (C.subgroupOf L).map q = (A.subgroupOf L).map q := by
    apply Subgroup.map_injective (f := MulAut.conj) conj_injective
    rw [←modelAction_image L e C hCL,←modelAction_image L e A hAL]
    have hC₀ : C.subgroupOf M = C₀ :=
      comap_map_eq_self_of_injective M.subtype_injective C₀
    rw [hC₀]
    exact hcomm
  have hpA : IsPPerfect 2 (A.subgroupOf L) :=
    (show IsPPerfect 2 A from isPPerfect_embedded_pResidual 2 (L ⊓ F.H)).of_surjective
      (subgroupOfEquivOfLe hAL).symm.toMonoidHom (subgroupOfEquivOfLe hAL).symm.surjective
  have hqker : q.ker = pCore 2 L :=
    (MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
  have hkn : q.ker ≤ normalizer (B.subgroupOf L : Set L) := by
    apply le_normalizer_iff.mpr
    intro k hk b hb
    have hkJ : (k : G) ∈ J := hTJ (InvariantFlag.localKernel_L_core_le_T L hTM
      (mem_map_of_mem L.subtype (hqker ▸ hk)))
    exact (mem_normalizer_iff.mp (hJY hkJ) b).mp hb
  have hAB : A.subgroupOf L ≤ B.subgroupOf L :=
    isPPerfect_le_of_map_le_of_kernel_normalizes q _ _ hpA
      (hqker ▸ pCore_isPGroup) hkn
      (hCim ▸ map_mono (subgroupOf_mono L hCB))
  intro a ha
  have hb : (a : G) ∈ B := hAB (show (⟨a,hAL ha⟩ : L) ∈ A.subgroupOf L from ha)
  exact (mem_map_iff_mem J.subtype_injective).mp hb

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
