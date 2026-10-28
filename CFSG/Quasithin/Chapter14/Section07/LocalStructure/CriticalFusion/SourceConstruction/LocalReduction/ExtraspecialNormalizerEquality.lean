module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizerBaumann
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms
public import Theory.SpecificGroups.PSL3Two.Parabolics.ResidualCommutator
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.GroupTheory.UniqueLocalResidualKernel

/-!
# The original extraspecial normalizer is H

Baumann control places the residual-quotient centralizer in N_G(L). The
actual three-prime supplement D = O₃′(N_G(K)) therefore acts on L/O₂(L).
Recognize the original L₁ image as a parabolic residual A₄ in SL₃(2).
Fixing its cubic quotient forces D's action to be inner in this A₄, so the
three-free action image is a two-group. Consequently O²(D) centralizes the
literal L quotient.

The commutator containment makes L normalize O²(D). Uniqueness of the
maximal two-local over LT, together with characteristic two in N_G(K),
kills this normal residual. Thus D ≤ O₂(N_G(K)) ≤ T ≤ H, and the already
proved supplement N_G(K) = H D gives N_G(K) = H and maximality of H.

This uses the original natural marking, not any later Data record. The
small quotient-action transports follow the independent argument in
Source.ResidualNormalizer.SectionCentralization, with its Data premise
replaced by the original HigherRankHypothesis.

Source: Aschbacher–Smith, 14.7.21(1), printed p.1050; the final uniqueness
argument uses the original maximal-overgroup property of LT.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
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
private theorem core_subgroupOf (A : Subgroup G) (hAL : A ≤ L) :
    (A.subgroupOf L).pCoreIn 2 = (A.pCoreIn 2).subgroupOf L := by
  apply map_injective L.subtype_injective
  rw [map_pCoreIn_of_injective 2 _ L.subtype L.subtype_injective,
    map_subgroupOf_eq_of_le hAL, map_subgroupOf_eq_of_le ((pCoreIn_le 2 A).trans hAL)]

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

private theorem modelAction_fixes_section (e : (L ⧸ pCore 2 L) ≃* SL)
    (A : Subgroup G) (hAL : A ≤ L) (X : Subgroup G)
    (hc : ⁅X,A⁆ ≤ A.pCoreIn 2) (x : normalizer (L : Set G)) (hx : (x : G) ∈ X) :
    ∀ a ∈ (A.subgroupOf L).map (modelMap L e),
      modelAction L e x a * a⁻¹ ∈ ((A.subgroupOf L).map (modelMap L e)).pCoreIn 2 := by
  have hk : IsPGroup 2 (modelMap L e).ker := by
    have he : (modelMap L e).ker = pCore 2 L := by
      exact (MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
    rw [he]
    exact pCore_isPGroup
  rintro _ ⟨a,ha,rfl⟩
  rw [modelAction_apply, ← map_inv, ← map_mul,
    ← map_pCoreIn_of_ker_isPGroup (modelMap L e) hk]
  apply mem_map_of_mem
  rw [core_subgroupOf L A hAL]
  exact hc (commutator_mem_commutator hx ha)

private theorem modelAction_inner_image (e : (L ⧸ pCore 2 L) ≃* SL)
    (A X : Subgroup G) (hAL : A ≤ L)
    (hn : X ≤ normalizer (A : Set G)) (hc : ⁅X,A⁆ ≤ A.pCoreIn 2)
    (P : Subgroup SL) (hP : P = pointParabolicSL ∨ P = lineParabolicSL)
    (hm : (A.subgroupOf L).map (modelMap L e) = residual P) :
    (X.subgroupOf (normalizer (L : Set G))).map (modelAction L e) ≤
      (A.subgroupOf (normalizer (L : Set G))).map (modelAction L e) := by
  rw [modelAction_image L e A hAL,hm]
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨g,hg,he⟩ := quotient_fixer_is_conj P hP (modelAction L e x)
    (by rw [← hm]; exact modelAction_preserves L e A x (hn hx))
    (by rw [← hm]; exact modelAction_fixes_section L e A hAL X hc x hx)
  exact ⟨g,hg,he.symm⟩

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
        ((F.Li L 1).subgroupOf L).map (modelMap L e) = residual P := by
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
  obtain ⟨_,_,_,_,g,P,hP,_,hmark,_,_⟩ := ResidualRecognition.recognize A R hp hc hn
  refine ⟨e₀.trans (MulAut.conj g),P,hP,?_⟩
  change A₀.map ((MulAut.conj g).toMonoidHom.comp f) = residual P
  rw [← map_map]
  exact hmark

private theorem threeFree_residual_centralizes_marked_quotient
    (e : (L ⧸ pCore 2 L) ≃* SL) (A D : Subgroup G)
    (hAL : A ≤ L) (hDM : D ≤ normalizer (L : Set G))
    (hn : D ≤ normalizer (A : Set G)) (hc : ⁅D,A⁆ ≤ A.pCoreIn 2)
    (hthree : Nat.Coprime 3 (Nat.card D))
    (P : Subgroup SL) (hP : P = pointParabolicSL ∨ P = lineParabolicSL)
    (hm : (A.subgroupOf L).map (modelMap L e) = residual P) :
    ⁅L,(pResidual 2 D).map D.subtype⁆ ≤ L.pCoreIn 2 := by
  let f : D →* MulAut SL := (modelAction L e).comp (inclusion hDM)
  have hI : f.range ≤ (residual P).map MulAut.conj := by
    rintro _ ⟨x,rfl⟩
    have hx := modelAction_inner_image L e A D hAL hn hc P hP hm
      (mem_map_of_mem (modelAction L e) (show inclusion hDM x ∈ D.subgroupOf (normalizer (L : Set G)) from x.property))
    rwa [modelAction_image L e A hAL,hm] at hx
  have h12 : Nat.card (residual P) = 12 := by
    rcases hP with rfl | rfl
    · exact card_point_residual
    · exact card_line_residual
  have hdiv : Nat.card f.range ∣ 12 := by
    have hd := (card_dvd_of_le hI).trans ((residual P).card_map_dvd MulAut.conj)
    rwa [h12] at hd
  have hcop : Nat.Coprime 3 (Nat.card f.range) := hthree.of_dvd_right
    (card_dvd_of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have hp : IsPGroup 2 f.range := isPGroup_iff_card_dvd_pow.mpr
    ⟨2, hcop.symm.dvd_of_dvd_mul_left (show Nat.card f.range ∣ 3 * 2 ^ 2 from hdiv)⟩
  have hker : pResidual 2 D ≤ f.ker := sInf_le
    ⟨inferInstance, hp.of_equiv (QuotientGroup.quotientKerEquivRange f).symm⟩
  rw [commutator_comm]
  apply commutator_le.mpr
  rintro x ⟨y,hy,rfl⟩ l hl
  let a : normalizer (L : Set G) := inclusion hDM y
  let b : L := ⟨l,hl⟩
  have ha : modelAction L e a = 1 := hker hy
  have hf : modelMap L e (L.normalizerMonoidHom a b) = modelMap L e b := by
    rw [← modelAction_apply,ha]
    rfl
  have hq : (L.normalizerMonoidHom a b) / b ∈ pCore 2 L := by
    apply QuotientGroup.eq_iff_div_mem.mp
    exact e.injective hf
  exact mem_map.mpr ⟨(L.normalizerMonoidHom a b) / b,hq,by
    change ((y : G) * l * (y : G)⁻¹) / l = ⁅(y : G),l⁆
    rw [div_eq_mul_inv,commutatorElement_def]⟩

/-- The residual of the actual three-prime supplement fixes the original
L/O₂(L), using the actual point-parabolic marking. -/
theorem extraspecial_normalizer_threePrime_residual_action
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let N := normalizer (K F : Set G)
    let D := (pPrimeCore 3 N).map N.subtype
    ⁅L,(pResidual 2 D).map D.subtype⁆ ≤ L.pCoreIn 2 := by
  let N := normalizer (K F : Set G)
  let D := (pPrimeCore 3 N).map N.subtype
  have hDC : D ≤ normalizerResidualCentralizer F := by
    rw [(extraspecial_normalizer_threePrime_supplement d h hab structural previous faithful earlier he).1]
    exact le_sup_right
  have hDM := hDC.trans (extraspecial_normalizer_centralizer_le_M d h hab structural previous faithful earlier he)
  have hDY := hDC.trans (extraspecial_normalizer_residualCentralizer_le_pointCentralizer
    h hab structural previous faithful he)
  have hn : D ≤ normalizer (F.Li L 1 : Set G) := (hDY.trans inf_le_left).trans
    (extraspecial_normalizer_normalizes_point h hab structural previous faithful he)
  have hc : ⁅D,F.Li L 1⁆ ≤ (F.Li L 1).pCoreIn 2 := by
    rw [commutator_comm]
    apply commutator_le_core_of_pCoreNormalizerAction_eq_one 2 (F.Li L 1) D hn
    intro x
    obtain ⟨a,ha,heq⟩ := (hDY x.property).2
    exact (show a = inclusion hn x from Subtype.ext heq) ▸ ha
  have hthree : Nat.Coprime 3 (Nat.card D) := by
    rw [card_map_of_injective N.subtype_injective]
    exact pPrimeCore_coprime_card
  obtain ⟨e,P,hP,hm⟩ := point_residual_marking (F := F) h structural
  exact threeFree_residual_centralizes_marked_quotient e (F.Li L 1) D
    ((F.Li_le L 1).trans inf_le_left) hDM hn hc hthree P hP hm

/-- The source three-prime supplement is contained in the original Sylow
subgroup: uniqueness kills its two-residual. -/
theorem extraspecial_normalizer_threePrime_le_core
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let N := normalizer (K F : Set G)
    (pPrimeCore 3 N).map N.subtype ≤ N.pCoreIn 2 := by
  let N := normalizer (K F : Set G)
  let D := (pPrimeCore 3 N).map N.subtype
  let Y := (pResidual 2 D).map D.subtype
  have hDN : D ≤ N := map_subtype_le _
  have hNY : N ≤ normalizer (Y : Set G) := by
    have hND : N ≤ normalizer (D : Set G) := by
      have hh := (pPrimeCore 3 N).le_normalizer_map N.subtype
      simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,N.range_subtype] using hh
    exact hND.trans (normalizer_le_normalizer_characteristic_image D (pResidual 2 D))
  have hND : N ≤ normalizer (D : Set G) := by
    have hh := (pPrimeCore 3 N).le_normalizer_map N.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,N.range_subtype] using hh
  have hTN : (T : Subgroup G) ≤ N := (F.invariant 1).trans (H_normalizes_K F)
  have hQ : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer (h.sylow_normalizes structural))
  have hQN : L.pCoreIn 2 ≤ N := by
    have hh := pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] at hh
    exact hQ.trans (hh.trans hTN)
  have hLY : L ≤ normalizer (Y : Set G) := normalizes_residual_of_commutator_le_two
    L N D (L.pCoreIn 2) hND hQN (isPGroup_pCoreIn 2 L)
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
    (extraspecial_normalizer_threePrime_residual_action d h hab structural previous faithful earlier he)
  have hu : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  have hNmax := (extraspecial_residual_normalizer_unique d h hab structural previous faithful he).1
  have hself : N ⊓ centralizer (N.pCoreIn 2 : Set G) ≤ N.pCoreIn 2 :=
    mem_He_iff.mpr (d.qtke.evenCharacteristic T N hNmax hTN)
  have hY : Y = ⊥ := normal_eq_bot_of_unique_core (L ⊔ (T : Subgroup G)) N
    (normalizer (L : Set G)) Y
    (fun M hM hAM => Set.mem_singleton_iff.mp ((h.maximal_unique structural hu).2 ▸
      show M ∈ {M : Subgroup G | IsMaximalTwoLocal M ∧ L ⊔ (T : Subgroup G) ≤ M} from ⟨hM,hAM⟩))
    (fun hn => h.flag_escape F previous ((H_normalizes_K F).trans hn)) hself
    ((map_subtype_le _).trans hDN) hNY (sup_le hLY (hTN.trans hNY))
  have hres : pResidual 2 D = ⊥ := (map_eq_bot_iff_of_injective _ D.subtype_injective).mp hY
  have hp : IsPGroup 2 D := (isPGroup_quotient_pResidual (G := D) 2).of_injective
    (QuotientGroup.mk' (pResidual 2 D)) (by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [QuotientGroup.ker_mk',hres])
  exact le_pCoreIn_of_normalizes hp hDN hND

/-- Source 14.7.21(1): the full extraspecial residual normalizer is the
original point normalizer, which is a maximal two-local subgroup. -/
theorem extraspecial_normalizer_eq_H
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    normalizer (K F : Set G) = F.H ∧ IsMaximalTwoLocal F.H := by
  let N := normalizer (K F : Set G)
  have hTN : (T : Subgroup G) ≤ N := (F.invariant 1).trans (H_normalizes_K F)
  have hQT : N.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN] using
      pCoreIn_le_sylow N (T.subtype hTN)
  have heq : N = F.H := by
    change normalizer (K F : Set G) = F.H
    rw [(extraspecial_normalizer_threePrime_supplement d h hab structural previous faithful earlier he).2.1]
    exact sup_eq_left.mpr ((extraspecial_normalizer_threePrime_le_core
      d h hab structural previous faithful earlier he).trans (hQT.trans (F.invariant 1)))
  exact ⟨heq,heq ▸ (extraspecial_residual_normalizer_unique d h hab structural previous faithful he).1⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
