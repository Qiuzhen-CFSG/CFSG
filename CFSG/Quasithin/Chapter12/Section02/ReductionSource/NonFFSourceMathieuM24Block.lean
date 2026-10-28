module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24BlockCore
public import Theory.GroupTheory.SylowCentralizerComplement
public import Theory.GroupTheory.CenterFreeOddImageCore
public import Theory.GroupTheory.SylowNormalRestriction
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuCocodeSylow
-- Internal continuation: unfold only the original component-action map.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPairCentralizers

/-!
# The original M24 cocode block and central involution

The completed selected-pair argument identifies V with O₂(L) and both
core commutators with V. The original irreducible action therefore makes L
a short group and a block in LT. Its literal quotient and block module
are identified with M24 and the eleven-dimensional cocode, including the
conjugation formula. The Sylow centralizer vanishes. Sylow averaging puts
Ω₁Z(T) in V, and the native cocode fixed-space bound makes it have order two.

The general block, Sylow-centralizer and averaging arguments adapt those in
NonFFSourceNonMathieuHermitianFieldFourBlock. Here they are private and use
only the underlying group-theoretic imports: that continuation's earlier
source interface conflicts with the Mathieu generation interface. The latter's
H≤C_G(Ω₁Z(T)) is explicitly transported to Ω₁Z(T)≤Z(H) using T≤H.

All core and normalization premises are discharged in the final application.
The actual cocode marking remains the earlier module-classification input.
The original involution-centralizer geometry, other Mathieu rows and ambient
J4 recognition remain with qt-d-1222-nonff-mathieu.
Source: Aschbacher–Smith 8.2.10 and the elementary-core argument in 8.2.12,
printed pp.721–722, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Stellmacher
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

private theorem m24_join_center_eq_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) : center (L ⊔ (T : Subgroup G) : Subgroup G) = ⊥ := by
  let F := D.fundamentalSetup h.toHypothesis1221
  have h127 := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hu := F.lemma_3_2_3_uniqueness h127
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (Chapter3.hasMaximalOutside_of_many T hmany F.maximalLocal hu.1
      ((show (T : Subgroup G) ≤ Chapter3.Section02.localJoin T L from le_sup_right).trans hu.2.1))
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) := by
    simpa only [Chapter3.Section02.FundamentalSetup.maximalLocal,D.localOrbit_eq] using hH
  have hcent := D.sourceOrbit_hstar_centralizes_omega h.toHypothesis1221 hnon hH'
  have hZ : omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype := by
    intro z hz
    have hzT := ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
    let zH : H := ⟨z,hH'.1.1.2 hzT⟩
    refine ⟨zH,?_,rfl⟩
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext ((hcent x.property z hz).symm)
  have hz := (F.qrcHypotheses h127 hH).center_eq_bot_of_omega_center_centralizes
    (h.simpleQTKE.evenCharacteristic T) hu.1 hu.2.2 hZ
  change center (Chapter3.Section02.localOrbit T L ⊔ (T : Subgroup G) : Subgroup G) = ⊥ at hz
  rw [D.localOrbit_eq] at hz
  exact hz

/-- The original Sylow centralizer and the component center vanish. This uses the
original multiple-overgroup and non-FF hypotheses, without a core identification. -/
private theorem m24_sylow_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ ∧ center L = ⊥ := by
  let J := L ⊔ (T : Subgroup G)
  let K := L.subgroupOf J
  let P := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hgen : K ⊔ (P : Subgroup J) = ⊤ := by
    change L.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤
    rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  have hbot := inf_centralizer_eq_bot_of_centerfree_sylow_supplement P K (pCore 2 J)
    hgen pCore_isPGroup (D.m24_join_center_eq_bot h hmany hnon)
  have hc : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
    apply bot_unique
    intro x hx
    have hxc : x ∈ centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
      rw [←D.sourceOrbit_eq,←hV]
      exact centralizer_le D.le_component hx.2
    obtain ⟨q,hq,hqx⟩ := (D.orbit_centralizer h.toHypothesis1221).le ⟨hx.1,hxc⟩
    change (q : G) = x at hqx
    have hqC : q ∈ centralizer (K : Set J) := by
      intro l hl
      apply Subtype.ext
      change (l : G)*(q : G)=(q : G)*(l : G)
      rw [hqx]
      exact hx.2 l hl
    exact mem_bot.mpr (hqx ▸ congrArg J.subtype (mem_bot.mp (hbot ▸ ⟨hq,hqC⟩)))
  refine ⟨hc,bot_unique ?_⟩
  intro z hz
  have hzQ : z ∈ pCore 2 L := by
    rw [←h.maximal_faithful.2.1.2.2]
    exact centralizer_generalizedFitting_le L (center_le_centralizer _ hz)
  have hQT : L.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 L).le_sylow_of_normalized T
      (D.sylow_normalizes_component.trans
        (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  apply Subtype.ext
  exact mem_bot.mp (hc ▸ ⟨hQT (mem_map_of_mem L.subtype hzQ),fun l hl =>
    congrArg L.subtype (mem_center_iff.mp hz ⟨l,hl⟩)⟩)

/-- The identified commutator layer makes the original component a short group. -/
private theorem m24_short_of_core_commutator
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hcomm : ⁅L.pCoreIn 2,L⁆ = D.sourceOrbit) :
    ChapterC.IsShort L := by
  have hB : (ChapterC.blockU L).map L.subtype = V := by
    rw [ChapterC.blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype]
    exact hcomm.trans hV.symm
  let eV : ChapterC.blockU L ≃* V :=
    ((ChapterC.blockU L).equivMapOfInjective L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr hB)
  let := D.elementary
  let : IsElementaryAbelian 2 (ChapterC.blockU L) :=
    IsElementaryAbelian.of_injective eV.toMonoidHom eV.injective
  have hz := (D.m24_sylow_centralizer h hmany hV hnon).2
  have hfix := (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1
  refine {
    finite := inferInstance
    twoPerfect := h.maximal_faithful.2.1.2.1
    fitting := h.maximal_faithful.2.1.2.2
    elementary := inferInstance
    central := ?_
    quotient := Or.inl h.quasisimple
    irreducible := ?_ }
  · intro u hu q hq
    apply Subtype.ext
    have hQ := (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
    exact (hQ (mem_map_of_mem L.subtype hq) u (hB ▸ mem_map_of_mem L.subtype hu)).symm
  · rw [ChapterC.BlockModuleIrreducible,hz,inf_bot_eq]
    refine ⟨bot_lt_iff_ne_bot.mpr ?_,?_⟩
    · intro he
      apply D.ne_bot
      rw [←hB,he,Subgroup.map_bot]
    · intro N hn _ hNU
      let := hn
      have hNV : N.map L.subtype ≤ V := (map_mono hNU).trans_eq hB
      have hLN : L ≤ normalizer (N.map L.subtype : Set G) := by
        simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
          N.le_normalizer_map L.subtype
      have hh := ReducedNormal.subspaceImage_eq_or_le_centralizer
        (L ⊔ (T : Subgroup G)) L le_sup_left D.irrPlus.isIrrPlus (N.map L.subtype)
        (by change _ ≤ subspaceImage _ D.space; rwa [D.image_eq]) hLN
      change N.map L.subtype = subspaceImage _ D.space ∨ _ at hh
      rw [D.image_eq] at hh
      rcases hh with he | hc
      · right
        exact map_injective L.subtype_injective (he.trans hB.symm)
      · left
        apply map_injective L.subtype_injective
        rw [Subgroup.map_bot]
        exact bot_unique ((le_inf hNV hc).trans hfix.le)

/-- The entire two-core of the original LT is elementary abelian: its squares
centralize L and lie in the trivial Sylow centralizer. -/
private theorem m24_elementary_join_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hcomm : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ = D.sourceOrbit) :
    IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)] using
      pCoreIn_le_sylow _ (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right))
  have hQC : Q ≤ centralizer (D.sourceOrbit : Set G) := hV ▸ D.core_centralizes
  have hpow (x : Q) : x^2=1 := by
    apply Subtype.ext
    apply mem_bot.mp
    rw [←(D.m24_sylow_centralizer h hmany hV hnon).1]
    refine ⟨hQT (Q.pow_mem x.property 2),?_⟩
    intro l hl
    let c := l*(x : G)*l⁻¹*(x : G)⁻¹
    have hc : c ∈ D.sourceOrbit := by
      rw [←hcomm,commutator_comm]
      exact commutator_mem_commutator hl x.property
    have hcx : Commute c (x : G) := hQC x.property c hc
    have hc2 : c^2=1 := elemPow_eq_one_of_isElementaryAbelian c hc
    have he : (l*(x : G)*l⁻¹)^2=(x : G)^2 := by
      calc
        _ = (c*(x : G))^2 := by congr 1; dsimp only [c]; group
        _ = c^2*(x : G)^2 := hcx.mul_pow 2
        _ = _ := by rw [hc2,one_mul]
    calc
      l*(x : G)^2 = (l*(x : G)*l⁻¹)^2*l := by simp only [pow_two]; group
      _ = (x : G)^2*l := by rw [he]
  exact {
    is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hpow x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }

/-- Odd-index Sylow averaging puts every central involution of T in the original
module, preserving the literal ambient centralizer. -/
private theorem m24_omega_center
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hcomm : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ = D.sourceOrbit) :
    omegaOneCenterAmbient (T : Subgroup G) =
      D.sourceOrbit ⊓ centralizer (T : Set G) := by
  let J := L ⊔ (T : Subgroup G)
  let K := L.subgroupOf J
  let W := D.sourceOrbit.subgroupOf J
  let P := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let : W.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.normalizes)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf
    (D.sourceOrbit_weakClosure_setup.le_sylow.trans (show (T : Subgroup G) ≤ J from le_sup_right))
  obtain ⟨S,hS⟩ := P.exists_sylow_map_eq_inf_of_normal K
  apply le_antisymm
  · intro z hz
    obtain ⟨hzT,hz2,hzC⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hz
    have hzQ : z ∈ J.pCoreIn 2 := by
      apply (D.orbit_centralizer h.toHypothesis1221).le
      refine ⟨hzT,?_⟩
      rw [←D.sourceOrbit_eq]
      exact centralizer_le D.sourceOrbit_weakClosure_setup.le_sylow hzC
    let zJ : J := ⟨z,mem_sup_right hzT⟩
    obtain ⟨w,hw,hwc⟩ := fixed_coset_of_sylow K W le_normalizer_of_normal
      (fun w hw => elemPow_eq_one_of_isElementaryAbelian w hw) S zJ
      (fun l hl => by
        change ⁅(l : G),z⁆ ∈ D.sourceOrbit
        rw [←hcomm,commutator_comm]
        exact commutator_mem_commutator hl hzQ)
      (fun l hl => by
        apply Subtype.ext
        exact hzC l ((hS ▸ mem_map_of_mem K.subtype hl).1))
    have hwt : (w : G)*z ∈ (T : Subgroup G) :=
      (T : Subgroup G).mul_mem (D.sourceOrbit_weakClosure_setup.le_sylow hw) hzT
    have hwL : (w : G)*z ∈ centralizer (L : Set G) := by
      intro l hl
      exact congrArg J.subtype (hwc ⟨l,mem_sup_left hl⟩ hl)
    have he : (w : G)*z=1 := mem_bot.mp
      ((D.m24_sylow_centralizer h hmany hV hnon).1 ▸ ⟨hwt,hwL⟩)
    have hzW : z ∈ D.sourceOrbit := by
      have he' : z=(w : G)⁻¹ := by
        simpa only [inv_mul_cancel_left,mul_one] using congrArg (fun x : G => (w : G)⁻¹*x) he
      rw [he']
      exact D.sourceOrbit.inv_mem hw
    exact ⟨hzW,hzC⟩
  · intro z hz
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨D.sourceOrbit_weakClosure_setup.le_sylow hz.1,
        elemPow_eq_one_of_isElementaryAbelian z hz.1,hz.2⟩

/-- The original fixed subgroup injects into the fixed line of an actual
Sylow subgroup of the marked M24 action. -/
theorem sourceOrbit_m24_cocode_fixed_card_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v)) :
    Nat.card (D.sourceOrbit ⊓ centralizer (T : Set G) : Subgroup G) ≤ 2 := by
  have hs := D.sourceOrbit_chapterK_of_many h hmany hnon hV
  have hsur := D.sourceOrbit_largeMathieu_component_surjective h.toHypothesis1221 hs (.inr hq)
  obtain ⟨S,hS⟩ := (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hST : (S : Subgroup L).map L.subtype ≤ (T : Subgroup G) := by
    rw [hS]
    exact inf_le_left.trans (by
      rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le
        (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)])
  let f := a.toMonoidHom.comp D.mathieuComponentAutomizer
  let P := S.mapSurjective (f := f) (a.surjective.comp hsur)
  let Z := D.sourceOrbit ⊓ centralizer (T : Set G)
  let F : Z → fixedSpace cocodeRepresentation P := fun z =>
    ⟨E (Additive.ofMul ⟨z,z.property.1⟩),by
      intro b
      obtain ⟨l,hl,hb⟩ := b.property
      change cocodeRepresentation (b : M24) (E (Additive.ofMul ⟨z,z.property.1⟩)) = _
      rw [←hb]
      change cocodeRepresentation (a (D.mathieuComponentAutomizer l))
        (E (Additive.ofMul ⟨z,z.property.1⟩)) = _
      rw [←hE]
      apply congrArg E
      apply Additive.toMul.injective
      apply Subtype.ext
      change (l : G)*(z : G)*(l : G)⁻¹=(z : G)
      rw [z.property.2 l (hST (mem_map_of_mem L.subtype hl)),mul_inv_cancel_right]⟩
  have hF : Function.Injective F := by
    intro x y he
    have he' := E.injective (congrArg Subtype.val he)
    exact Subtype.ext (congrArg (fun v : Additive D.sourceOrbit => (v.toMul : G)) he')
  exact (Nat.card_le_card_of_injective F hF).trans
    (Chapter7.NormalizedSource.MathieuCocodeSylow.fixed_card_le_two P)

/-- The literal quotient L/O₂(L) and block module U(L)/C_U(L)(L)
carry the marked eleven-dimensional M24 cocode representation. -/
theorem sourceOrbit_m24_cocode_block_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hcomm : ⁅L.pCoreIn 2,L⁆ = D.sourceOrbit)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v)) :
    ChapterC.IsLinearBlockModel L cocodeRepresentation := by
  have hB : (ChapterC.blockU L).map L.subtype = D.sourceOrbit := by
    rw [ChapterC.blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype]
    exact hcomm
  have hz : ChapterC.blockFixed L=⊥ := by
    change (center L).subgroupOf (ChapterC.blockU L)=⊥
    rw [(D.m24_sylow_centralizer h hmany hV hnon).2,bot_subgroupOf]
  let eV : ChapterC.blockU L ≃* D.sourceOrbit :=
    ((ChapterC.blockU L).equivMapOfInjective L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr hB)
  let eW : D.sourceOrbit ≃* Multiplicative Cocode := {
    toFun v := Multiplicative.ofAdd (E (Additive.ofMul v))
    invFun w := (E.symm w.toAdd).toMul
    left_inv v := by exact congrArg Additive.toMul (E.symm_apply_apply (Additive.ofMul v))
    right_inv w := by exact congrArg Multiplicative.ofAdd (E.apply_symm_apply w.toAdd)
    map_mul' x y := congrArg Multiplicative.ofAdd (E.map_add (Additive.ofMul x) (Additive.ofMul y)) }
  let f := a.toMonoidHom.comp D.mathieuComponentAutomizer
  have hfk : f.ker = pCore 2 L :=
    (MonoidHom.ker_comp_of_injective D.mathieuComponentAutomizer
      a.toMonoidHom a.injective).trans
      (D.sourceOrbit_largeMathieu_component_kernel h.toHypothesis1221 (.inr hq))
  have hsur := D.sourceOrbit_largeMathieu_component_surjective h.toHypothesis1221
    (D.sourceOrbit_chapterK_of_many h hmany hnon hV) (.inr hq)
  let q : (L ⧸ pCore 2 L) ≃* M24 :=
    (QuotientGroup.quotientMulEquivOfEq hfk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f (a.surjective.comp hsur))
  let e0 : ChapterC.BlockModule L ≃* ChapterC.blockU L :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  let r : M24 →* MulAut (Multiplicative Cocode) := {
    toFun b := (LinearMap.GeneralLinearGroup.toLinearEquiv (cocodeRepresentation.asGroupHom b)).toAddEquiv.toMultiplicative
    map_one' := by
      apply MulEquiv.ext
      intro v
      apply Multiplicative.toAdd.injective
      change cocodeRepresentation 1 v.toAdd = v.toAdd
      rw [map_one]
      rfl
    map_mul' x y := by
      apply MulEquiv.ext
      intro v
      apply Multiplicative.toAdd.injective
      change cocodeRepresentation (x*y) v.toAdd = cocodeRepresentation x (cocodeRepresentation y v.toAdd)
      rw [map_mul]
      rfl }
  refine ⟨r,⟨{quotientIso := q,moduleIso := (e0.trans eV).trans eW,intertwining := ?_}⟩,
    fun _ _ => rfl⟩
  intro l u
  apply Multiplicative.toAdd.injective
  change E (Additive.ofMul (eV (ChapterC.blockConjugate L l u))) =
    cocodeRepresentation (a (D.mathieuComponentAutomizer l)) (E (Additive.ofMul (eV u)))
  exact hE (D.mathieuComponentAutomizer l) (Additive.ofMul (eV u))

/-- Source 8.2.10 for the actual marked M24 cocode branch. The block
is subnormal in LT and has the literal cocode action; its core is V,
its Sylow centralizer is trivial, and its original fixed subgroup has order two. -/
theorem sourceOrbit_m24_cocode_block_structure
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v)) :
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ = D.sourceOrbit ∧
      ⁅L.pCoreIn 2,L⁆ = D.sourceOrbit ∧ D.sourceOrbit = L.pCoreIn 2 ∧
      ChapterC.IsShort L ∧
      ChapterC.IsBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) ∧
      ChapterC.IsLinearBlockModel L cocodeRepresentation ∧
      (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ ∧ center L = ⊥ ∧
      IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      omegaOneCenterAmbient (T : Subgroup G) = D.sourceOrbit ⊓ centralizer (T : Set G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2 := by
  obtain ⟨hJ,hL,hcore⟩ := D.sourceOrbit_m24_cocode_block_core h hmany hV hq hnon a E hE
  have hcen := D.m24_sylow_centralizer h hmany hV hnon
  have hz := D.m24_omega_center h hmany hV hnon hJ
  have hb := D.m24_short_of_core_commutator h hmany hV hnon hL
  have hblock : ChapterC.IsBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) := {
    finite := inferInstance
    short := ChapterC.RankOne.Solvable.isShort_of_equiv
      (subgroupOfEquivOfLe (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm hb
    subnormal := h.maximal_faithful.1.1.1.subnormal }
  refine ⟨hJ,hL,hcore,hb,hblock,D.sourceOrbit_m24_cocode_block_model h hmany hV hq hnon hL a E hE,
    hcen.1,hcen.2,D.m24_elementary_join_core h hmany hV hnon hJ,hz,?_⟩
  rw [hz]
  have hle := D.sourceOrbit_m24_cocode_fixed_card_le h hmany hV hq hnon a E hE
  have hne := inf_centralizer_ne_bot_of_pGroups (T : Subgroup G) D.sourceOrbit T.isPGroup'
    (IsElementaryAbelian.isPGroup 2 D.sourceOrbit)
    D.sourceOrbit_weakClosure_setup.normalizes D.sourceOrbit_weakClosure_setup.nontrivial
  have hgt := (one_lt_card_iff_ne_bot _).mpr hne
  change 1 < Nat.card (D.sourceOrbit ⊓ centralizer (T : Set G) : Subgroup G) at hgt
  exact Nat.le_antisymm hle (by omega)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
