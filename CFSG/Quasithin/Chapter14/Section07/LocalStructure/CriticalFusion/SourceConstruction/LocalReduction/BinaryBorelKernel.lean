module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCoreContainment
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SourceActions.MarkedImages
public import Theory.GroupTheory.CubicAutomorphismLines
public import Theory.GroupTheory.PResidual.KernelSupplement
public import Theory.GroupTheory.TwoPerfectNormalizerControl
public import Theory.GroupTheory.TwoByThreeDisplacement

/-!
# The original Borel action kernel and point-cubic inverter

Let B be a two-perfect subgroup of N_G(L) containing and normalizing the
original point group L₁. Its action on L/O₂(L) preserves the actual marked
A₄ in PSL₃(2). Two-perfectness identifies the action image with that A₄,
so B = L₁ B_C for B_C = O²(C_B(L/O₂(L))). This is an equality of the original
subgroups, retaining the entire action kernel.

Every common normalizer of B and L normalizes B_C. For t in L normalizing B,
[B_C,t] lies in B_C ∩ O₂(L), a normal two-subgroup of B_C. Thus t fixes
B_C/O₂(B_C). The same marked parabolic supplies a genuine inverter in T∩L
of L₁/O₂(L₁): trivial action would contradict [A₄,D₈] = A₄.

Applied to B = O²(B₀), the literal odd torus map gives E = P D with P the
point cubic and D the fixed image of B_C. No raw index-three assertion for
B_C in B is used; the cubic bound belongs to the torus quotient.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1056,
refs/quasithin.pdf. The private marked-action transport refines the same
original-point construction in ThreeCoreContainment.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
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


/-- The literal action of B on the original L/O₂(L). -/
@[expose] def binaryBorelAction (L B : Subgroup G)
    (hBM : B ≤ normalizer (L : Set G)) : B →* MulAut (L ⧸ pCore 2 L) :=
  (normalizerQuotientAction L (pCore 2 L)).comp (inclusion hBM)

/-- O²(C_B(L/O₂(L))), embedded in the original ambient group. -/
@[expose] def binaryBorelCentralResidual (L B : Subgroup G)
    (hBM : B ≤ normalizer (L : Set G)) : Subgroup G :=
  ((pResidual 2 (binaryBorelAction L B hBM).ker).map
    (binaryBorelAction L B hBM).ker.subtype).map B.subtype

/-- The actual two-perfect Borel is supplemented by the residual of its
literal quotient-action kernel and the original point group. -/
theorem point_borel_kernel_supplement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
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

/-- The residual kernel is normalized by every common normalizer of B and L. -/
theorem binaryBorelCentralResidual_normalized
    (L B : Subgroup G) (hBM : B ≤ normalizer (L : Set G)) :
    normalizer (B : Set G) ⊓ normalizer (L : Set G) ≤
      normalizer (binaryBorelCentralResidual L B hBM : Set G) := by
  let M := normalizer (L : Set G)
  let a := normalizerQuotientAction L (pCore 2 L)
  let C := (binaryBorelAction L B hBM).ker.map B.subtype
  have hC : C = B ⊓ a.ker.map M.subtype := by
    ext x
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact ⟨b.property, inclusion hBM b,hb,rfl⟩
    · rintro ⟨hb,y,hy,hyx⟩
      refine ⟨⟨x,hb⟩,?_,rfl⟩
      have hey : inclusion hBM (⟨x,hb⟩ : B) = y := Subtype.ext hyx.symm
      change a (inclusion hBM (⟨x,hb⟩ : B)) = 1
      rw [hey]
      exact hy
  have hMC : M ≤ normalizer (a.ker.map M.subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      a.ker.le_normalizer_map M.subtype
  have hn : normalizer (B : Set G) ⊓ M ≤ normalizer (C : Set G) := by
    rw [hC]
    exact (le_inf inf_le_left (inf_le_right.trans hMC)).trans
      inf_normalizer_le_normalizer_inf
  have he : binaryBorelCentralResidual L B hBM =
      (pResidual 2 C).map C.subtype := map_embedded_pResidual 2 _ B.subtype
  rw [he]
  exact hn.trans (normalizer_le_normalizer_characteristic_image C (pResidual 2 C))

/-- A normalizing element of L fixes the intrinsic two-core quotient of
O²(C_B(L/O₂(L))). The intersection with O₂(L) is taken inside this kernel. -/
theorem binaryBorelCentralResidual_fixed
    (L B : Subgroup G) (hBM : B ≤ normalizer (L : Set G))
    {t : G} (htL : t ∈ L) (htB : t ∈ normalizer (B : Set G)) :
    coreAction (binaryBorelCentralResidual L B hBM)
      ⟨t,binaryBorelCentralResidual_normalized L B hBM ⟨htB,L.le_normalizer htL⟩⟩ = 1 := by
  let C := binaryBorelCentralResidual L B hBM
  have hCB : C ≤ B := map_subtype_le _
  have hCM : C ≤ normalizer (L : Set G) := hCB.trans hBM
  have hc : ⁅L,C⁆ ≤ L.pCoreIn 2 := by
    apply commutator_le_of_normalizerQuotientAction_eq_one L C (pCore 2 L) hCM
    rintro ⟨x,hx⟩
    obtain ⟨b,⟨c,hc,rfl⟩,rfl⟩ := hx
    exact c.property
  have hi : L.pCoreIn 2 ⊓ C ≤ C.pCoreIn 2 :=
    pCoreIn_inf_le_of_normalizes hCM
  apply (coreAction_eq_one_iff _ _).mpr
  intro c
  have hh : t * (c : G) * t⁻¹ * (c : G)⁻¹ ∈ C.pCoreIn 2 :=
    hi ⟨hc (commutator_mem_commutator htL c.property),
      C.mul_mem ((mem_normalizer_iff.mp
        (binaryBorelCentralResidual_normalized L B hBM ⟨htB,L.le_normalizer htL⟩) c).mp
          c.property) (C.inv_mem c.property)⟩
  exact (mem_map_iff_mem C.subtype_injective).mp hh

/-- The actual Sylow intersection T∩L contains an inverter of the original
point cubic. Its existence follows from the marked parabolic commutator,
not from an additional local-action premise. -/
theorem exists_point_core_inverter
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
      ∀ x : F.Li L 1 ⧸ pCore 2 (F.Li L 1),
        coreAction (F.Li L 1)
          ⟨t,ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes structural) t.property.1⟩ x = x⁻¹ := by
  let A := F.Li L 1
  let S := (T : Subgroup G) ⊓ L
  have hn : S ≤ normalizer (A : Set G) :=
    inf_le_left.trans (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes structural))
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
    (pointResidual_core_quotient_card (F := F) h structural) _).resolve_left ht⟩

/-- For the original Borel, the torus is the product of the point cubic
and the fixed image of the actual centralizer residual. -/
theorem point_borel_torus_supplement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (B₀ : Subgroup G) (hBM : B₀ ≤ normalizer (L : Set G))
    (hAB : F.Li L 1 ≤ (pResidual 2 B₀).map B₀.subtype)
    (hBA : B₀ ≤ normalizer (F.Li L 1 : Set G))
    {E : Type*} [Group E] [Finite E] (f : B₀ →* E)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) (ho : Odd (Nat.card E))
    (t : G) (htL : t ∈ L) (htB : t ∈ normalizer (B₀ : Set G))
    (α : MulAut E) (heq : ∀ b : B₀, α (f b) = f (B₀.normalizerMonoidHom ⟨t,htB⟩ b)) :
    let B := (pResidual 2 B₀).map B₀.subtype
    let hB := (map_subtype_le (pResidual 2 B₀)).trans hBM
    let C := binaryBorelCentralResidual L B hB
    let P := SourceActions.Markings.image B₀ (F.Li L 1) f
    let D := SourceActions.Markings.image B₀ C f
    P ⊔ D = ⊤ ∧ (∀ x ∈ D, α x = x) := by
  let B := (pResidual 2 B₀).map B₀.subtype
  have hBB : B ≤ B₀ := map_subtype_le _
  have hB := hBB.trans hBM
  let C := binaryBorelCentralResidual L B hB
  have hCB : C ≤ B := map_subtype_le _
  have hgen := point_borel_kernel_supplement h structural B hB
    (isPPerfect_embedded_pResidual 2 B₀) hAB (hBB.trans hBA)
  have hsup : (F.Li L 1).subgroupOf B₀ ⊔ C.subgroupOf B₀ = B.subgroupOf B₀ := by
    apply map_injective B₀.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (hAB.trans hBB),
      map_subgroupOf_eq_of_le (hCB.trans hBB),map_subgroupOf_eq_of_le hBB]
    exact hgen
  have honto : (B.subgroupOf B₀).map f = ⊤ := by
    have hh := MonoidHom.range_eq_top.mpr (SourceActions.Markings.residual_surjective B₀ f hf ho)
    rwa [MonoidHom.range_comp,inclusion_range] at hh
  refine ⟨?_,?_⟩
  · change ((F.Li L 1).subgroupOf B₀).map f ⊔ (C.subgroupOf B₀).map f = ⊤
    rw [←Subgroup.map_sup,hsup,honto]
  · have htB' : t ∈ normalizer (B : Set G) :=
      normalizer_le_normalizer_characteristic_image B₀ (pResidual 2 B₀) htB
    exact SourceActions.Markings.image_fixed B₀ C (hCB.trans hBB) f hk ho ⟨t,htB⟩
      (binaryBorelCentralResidual_normalized L B hB ⟨htB',L.le_normalizer htL⟩)
      α heq (binaryBorelCentralResidual_fixed L B hB htL htB')

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
