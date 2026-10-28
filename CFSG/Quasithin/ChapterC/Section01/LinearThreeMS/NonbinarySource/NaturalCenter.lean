module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.CentralSections
public import Theory.Representation.SpecialLinearThreeTransitivity
public import Theory.Representation.FirstCohomologyConjugationSplitting

/-!
# Whole natural central sections and descent at field four

Let Q=[O₂(KR),K] in a genuine nonbinary linear-three MS-pair. If Z(Q)
or its whole moved subgroup [Z(Q),K] is natural, transitivity on nonzero
vectors identifies that entire subgroup with the original initial moved
layer. In particular the natural moved center centralizes O₂(KR).

When [Z(Q),K] is natural, the three-subgroup lemma then shows that
[Z(Q),O₂(K)] is K-fixed. It lies in the fixed-free initial moved layer,
so is trivial. Thus the action on the entire center descends faithfully
to the supplied full SL₃ quotient, including at field four. Vanishing of
H¹ for the nonbinary natural module splits the entire Z(Q) into its moved
subgroup and its K-fixed subgroup, with the actual conjugation marking.

These are conditional whole-section results. Recognition of the whole
moved center, identification of its fixed subgroup with all of C_Q(K),
the fixed-factor order, the upper Frattini sections and the remaining
Sylow radical inequalities still require the C.1.34 source argument.
No ambient centrality of the fixed factor is assumed or concluded.
The original nonblock and point applications are in NonblockMSClassification
and PointApplication.

Source: Aschbacher--Smith C.1.34(3)--(4), printed pp.136--137, and
I.1.6(4), printed p.408; original 4.3.8--10 and 11.1.5.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.NaturalCenter
open Chapter1.RadicalExclusions.ModelReduction.FullSieve SourceInterface
variable {G : Type*} [Group G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F]

private theorem eq_of_natural {U A : Subgroup G}
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K U ⊥ (linearThreeActor e) (specialLinearNatural (k := F) 3))
    (hAU : A ≤ U) (hKA : K ≤ normalizer (A : Set G)) (hne : A ≠ ⊥) : A = U := by
  have hKU := hm.2.1
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hbot,a,ha⟩ := hm
  let := hbot
  let E : U ≃* Multiplicative (Fin 3 → F) := QuotientGroup.quotientBot.symm.trans a
  obtain ⟨u,hu,hu1⟩ := A.bot_or_exists_ne_one.resolve_left hne
  let uu : U := ⟨u,hAU hu⟩
  have hune : (E uu).toAdd ≠ 0 := by
    intro hz
    exact hu1 (congrArg Subtype.val (E.map_eq_one_iff.mp (Multiplicative.toAdd.injective hz)))
  apply le_antisymm hAU
  intro x hx
  by_cases hx1 : x = 1
  · exact hx1 ▸ A.one_mem
  let xx : U := ⟨x,hx⟩
  have hxne : (E xx).toAdd ≠ 0 := by
    intro hz
    exact hx1 (congrArg Subtype.val (E.map_eq_one_iff.mp (Multiplicative.toAdd.injective hz)))
  obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three _ _ hune hxne
  obtain ⟨k,hk⟩ := e.surjective.comp (QuotientGroup.mk'_surjective _) g
  let y : U := U.normalizerMonoidHom ⟨k,hKU k.property⟩ uu
  have hy : (y : G) = k * u * (k : G)⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
  have he : E y = E xx := by
    apply Multiplicative.toAdd.injective
    change (a (QuotientGroup.mk' ⊥ y)).toAdd = _
    rw [ha k uu y hy]
    change specialLinearNatural 3 (e (QuotientGroup.mk' _ k)) (E uu).toAdd = _
    rw [show e (QuotientGroup.mk' _ k) = g from hk]
    exact hg
  have hxy : x = k * u * (k : G)⁻¹ :=
    (congrArg Subtype.val (E.injective he)).symm.trans hy
  rw [hxy]
  exact (mem_normalizer_iff.mp (hKA k.property) u).mp hu

variable [Finite G] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "Q" => msQ K R
local notation "Z" => SourceInterface.centerIn Q

include h hn
omit [CharP F 2] in
private theorem initial_ne_bot : initialMoved K R ≠ ⊥ := by
  intro hu
  have hc : K ≤ centralizer (initialOmega K R : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hu)
  apply component_not_le_centralOmegaKernel h hn
  intro k hk v hv
  exact Subtype.ext (hc hk v (mem_map_of_mem _ hv))

omit [CharP F 2] in
/-- A natural whole center equals the original initial moved subgroup, including at field four. -/
theorem center_eq_initial
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K Z ⊥ (linearThreeActor e) (specialLinearNatural (k := F) 3)) :
    Z = initialMoved K R :=
  (eq_of_natural e hm initialMoved_le_core_center (normalizer_commutator_ge_right _ _) (initial_ne_bot h hn)).symm

omit [CharP F 2] in
/-- Thus the whole natural center centralizes the original join two-core. -/
theorem center_centralizes_joinCore
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K Z ⊥ (linearThreeActor e) (specialLinearNatural (k := F) 3)) :
    Z ≤ centralizer ((K ⊔ R).pCoreIn 2 : Set G) := by
  rw [center_eq_initial h hn e hm]
  exact initialMoved_centralizes_joinCore

omit [CharP F 2] in
/-- A natural whole moved center is exactly the initial moved subgroup.
No centrality of the component-fixed part of Z(Q) is used. -/
theorem centerCommutator_eq_initial
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K ⁅Z,K⁆ ⊥ (linearThreeActor e) (specialLinearNatural (k := F) 3)) :
    ⁅Z,K⁆ = initialMoved K R := by
  have hid : ⁅initialMoved K R,K⁆ = initialMoved K R := by
    apply commutator_isPPerfect_idempotent K (initialOmega K R) (component_twoPerfect h hn)
    · rw [initialOmega_eq]
      exact IsElementaryAbelian.isPGroup 2 _
    · rw [initialOmega_eq]
      exact (le_sup_left : K ≤ (K ⊔ R : Subgroup G)).trans (((K ⊔ R : Subgroup G)).le_normalizer.trans
        ((normalizer_le_normalizer_characteristic_image (K ⊔ R : Subgroup G) (pCore 2 (K ⊔ R : Subgroup G))).trans
          (normalizer_le_normalizer_omegaCenterIn ((K ⊔ R : Subgroup G).pCoreIn 2))))
  have hle : initialMoved K R ≤ ⁅Z,K⁆ := by
    rw [←hid]
    exact commutator_mono initialMoved_le_core_center le_rfl
  exact (eq_of_natural e hm hle (normalizer_commutator_ge_right _ _) (initial_ne_bot h hn)).symm

omit [CharP F 2] in
/-- The actual natural moved center centralizes the join two-core, also at field four. -/
theorem centerCommutator_centralizes_joinCore
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K ⁅Z,K⁆ ⊥ (linearThreeActor e) (specialLinearNatural (k := F) 3)) :
    ⁅Z,K⁆ ≤ centralizer ((K ⊔ R).pCoreIn 2 : Set G) := by
  rw [centerCommutator_eq_initial h hn e hm]
  exact initialMoved_centralizes_joinCore

/-- Recognition of the whole moved center removes the field-four obstruction
on the entire center: the intrinsic component core acts trivially there. -/
theorem center_centralizes_componentCore
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K ⁅Z,K⁆ ⊥ (linearThreeActor e) (specialLinearNatural (k := F) 3)) :
    Z ≤ centralizer (K.pCoreIn 2 : Set G) := by
  let O := K.pCoreIn 2
  have hON : O ≤ (K ⊔ R).pCoreIn 2 := pCoreIn_mono_of_normalizes le_sup_left
    ((normal_subgroupOf_iff_le_normalizer (show K ≤ K ⊔ R from le_sup_left)).mp (component_normal h hn))
  have hUZ : ⁅Z,K⁆ ≤ centralizer (O : Set G) :=
    (centerCommutator_centralizes_joinCore h hn e hm).trans (centralizer_le hON)
  have hZQ : Z ≤ centralizer (Q : Set G) := by
    rintro z ⟨z,hz,rfl⟩ q hq
    exact congrArg (Q).subtype (mem_center_iff.mp hz ⟨q,hq⟩)
  have htriple : ⁅⁅Z,O⁆,K⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · rw [←msQ_eq_intrinsic h hn]
      exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hZQ)
    · rw [commutator_comm K Z]
      exact commutator_eq_bot_iff_le_centralizer.mpr hUZ
  have hmove : ⁅Z,O⁆ ≤ initialMoved K R :=
    (commutator_mono le_rfl (pCoreIn_le 2 K)).trans_eq (centerCommutator_eq_initial h hn e hm)
  have hz : ⁅Z,O⁆ = ⊥ := bot_unique
    ((le_inf hmove (le_inf (hmove.trans initialMoved_le_omega)
      (commutator_eq_bot_iff_le_centralizer.mp htriple))).trans_eq (initialMoved_split h hn).2)
  exact commutator_eq_bot_iff_le_centralizer.mp hz

/-- The whole center splits over its actual natural moved subgroup at every
nonbinary field. The fixed factor is only asserted to centralize K. -/
theorem center_split
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K ⁅Z,K⁆ ⊥ (linearThreeActor e) (specialLinearNatural (k := F) 3)) :
    ⁅Z,K⁆ ⊔ (Z ⊓ centralizer (K : Set G)) = Z ∧
      ⁅Z,K⁆ ⊓ (Z ⊓ centralizer (K : Set G)) = ⊥ := by
  have hKU := hm.2.1
  have hUZ : ⁅Z,K⁆ ≤ Z := le_normalizer_iff_commutator_le_left.mp
    ((le_sup_left : K ≤ K ⊔ R).trans (CentralSections.join_normalizes_center h hn))
  have hcentral := center_centralizes_componentCore h hn e hm
  have hmatch := centerCommutator_eq_initial h hn e hm
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,hbot,a,ha⟩ := hm
  let := hbot
  let E : (⁅Z,K⁆ : Subgroup G) ≃* Multiplicative (Fin 3 → F) :=
    QuotientGroup.quotientBot.symm.trans a
  have hE (k : K) (v : Fin 3 → F) :
      (E.symm (Multiplicative.ofAdd (specialLinearNatural 3 (linearThreeActor e k) v)) : G) =
        k * (E.symm (Multiplicative.ofAdd v) : G) * (k : G)⁻¹ := by
    let x := E.symm (Multiplicative.ofAdd v)
    let y : (⁅Z,K⁆ : Subgroup G) := (⁅Z,K⁆ : Subgroup G).normalizerMonoidHom ⟨k,hKU k.property⟩ x
    have hy : (y : G) = k * (x : G) * (k : G)⁻¹ := normalizerMonoidHom_apply_apply_coe _ _ _
    have he := ha k x y hy
    change (E y).toAdd = specialLinearNatural 3 (linearThreeActor e k) (E x).toAdd at he
    have hx : E x = Multiplicative.ofAdd v := E.apply_symm_apply _
    rw [hx] at he
    exact (congrArg (fun w => (E.symm w : G)) (Multiplicative.toAdd.injective he)).symm.trans
      ((congrArg Subtype.val (E.symm_apply_apply y)).trans hy)
  have hF : 2 < Nat.card F := by
    rw [h.field_card]
    have hh := Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) hn
    simpa using hh
  let := OneCohomology.SLHigherNatural.H1_subsingleton_sl3_large_field hF
  refine ⟨OneCohomology.sup_centralizer_eq_of_conjugation_H1 K Z ⁅Z,K⁆ hUZ
    (linearThreeActor e) (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (specialLinearNatural 3) E hE ?_ ?_, ?_⟩
  · intro k hk z hz
    have hkO : (k : G) ∈ K.pCoreIn 2 := by
      apply mem_map_of_mem K.subtype
      exact (QuotientGroup.eq_one_iff k).mp (e.map_eq_one_iff.mp hk)
    exact (hcentral hz k hkO).symm
  · intro k z
    change ⁅(k : G),(z : G)⁆ ∈ (⁅Z,K⁆ : Subgroup G)
    rw [commutator_comm]
    exact commutator_mem_commutator k.property z.property
  · apply bot_unique
    rintro x ⟨hx,hxz,hxk⟩
    have hxI := hmatch.le hx
    exact (initialMoved_split h hn).2.le ⟨hxI,initialMoved_le_omega hxI,hxk⟩


/-- The whole center has a faithful action of the original full SL₃, including
field four, once its whole moved center is natural. -/
theorem exists_centerAction
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K ⁅Z,K⁆ ⊥ (linearThreeActor e) (specialLinearNatural (k := F) 3)) :
    ∃ b : SL(3,F) →* MulAut Z, Function.Injective b ∧
      ∀ (k : K) (z : Z), (b (linearThreeActor e k) z : G) =
        k * (z : G) * (k : G)⁻¹ := by
  let J := K ⊔ R
  let hnorm : K ≤ normalizer (Z : Set G) :=
    (le_sup_left : K ≤ J).trans (CentralSections.join_normalizes_center h hn)
  let a : K →* MulAut Z := (Z).normalizerMonoidHom.comp (inclusion hnorm)
  have ha (k : K) (z : Z) : (a k z : G) = k * (z : G) * (k : G)⁻¹ := rfl
  have hker : a.ker = pCore 2 K := by
    apply le_antisymm
    · have hmap : a.ker.map K.subtype ≤ J.pCoreIn 2 := by
        rintro x ⟨k,hk,rfl⟩
        let j : J := ⟨k,mem_sup_left k.property⟩
        apply mem_map_of_mem J.subtype (x := j)
        apply (initialMoved_join_centralizer h hn).le
        intro u hu
        have hu' : (u : G) ∈ initialMoved K R := by
          have hh := mem_map_of_mem J.subtype hu
          rw [map_commutator,map_subgroupOf_eq_of_le (show K ≤ J from le_sup_left)] at hh
          exact hh
        have he := congrArg (fun t : MulAut Z => (t ⟨u,initialMoved_le_core_center hu'⟩ : G)) hk
        change (k : G) * (u : G) * (k : G)⁻¹ = u at he
        exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp he).symm
      have hp : IsPGroup 2 a.ker :=
        ((isPGroup_pCoreIn 2 J).to_le hmap).of_injective
          (a.ker.equivMapOfInjective K.subtype K.subtype_injective).toMonoidHom
          (a.ker.equivMapOfInjective K.subtype K.subtype_injective).injective
      exact le_sSup ⟨inferInstance,hp⟩
    · intro k hk
      apply MulEquiv.ext
      intro z
      apply Subtype.ext
      change (k : G) * (z : G) * (k : G)⁻¹ = z
      rw [center_centralizes_componentCore h hn e hm z.property k
        (mem_map_of_mem K.subtype hk),mul_inv_cancel_right]
  let b : SL(3,F) →* MulAut Z :=
    (QuotientGroup.lift (pCore 2 K) a hker.ge).comp e.symm.toMonoidHom
  have hb (k : K) : b (linearThreeActor e k) = a k := by
    change QuotientGroup.lift (pCore 2 K) a hker.ge
      (e.symm (e (QuotientGroup.mk' (pCore 2 K) k))) = a k
    rw [e.symm_apply_apply]
    rfl
  refine ⟨b,?_,fun k z => by rw [hb]; exact ha k z⟩
  apply (MonoidHom.ker_eq_bot_iff b).mp
  apply bot_unique
  intro g hg
  obtain ⟨k,rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 K)) g
  have hk : k ∈ a.ker := by
    change a k = 1
    rw [←hb]
    exact hg
  change e (QuotientGroup.mk' (pCore 2 K) k) = 1
  exact e.map_eq_one_iff.mpr ((QuotientGroup.eq_one_iff k).mpr (hker.le hk))


end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.NaturalCenter
