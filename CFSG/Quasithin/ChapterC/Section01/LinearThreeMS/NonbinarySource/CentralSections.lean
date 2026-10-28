module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.CentralCore
public import Theory.SpecificGroups.SL3.CommutatorCentralCover

/-!
# Central sections of the whole nonbinary MS core

Write Q=[O₂(KR),K]. The initial moved omega layer lies in Ω₁(Z(Q)),
so the centralizers of Z(Q), Ω₁(Z(Q)), and [Z(Q),K] lie in O₂(KR).
The group Q acts trivially on these sections. Consequently each actual
component image is a perfect central cover of the original full SL₃.
Outside field four the scalar-cover lift removes its kernel, giving a
faithful action with the original quotient marking and literal conjugation.
In particular the entire Z(Q) centralizes the intrinsic O₂(K), without
assuming Q is abelian or central in O₂(KR).

For every nonbinary field, including field four, MS3 also supplies an
FF-offender on the entire Ω₁(Z(Q)) through its actual centralizer quotient.
The section is taken from the whole commutator core, not its initial layer.
These inputs are applied to the original Chapter 4 nonblock and Chapter 11
point configurations. Natural-module recognition, the exceptional covering
kernel, the Frattini sections and the Sylow radical inequalities remain
separate obligations in C.1.34.

Source: Aschbacher--Smith C.1.31--34, printed pp.135--137, I.1.3,
printed p.407, and the original 4.3.8--10 and 11.1.5.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.CentralSections
open Chapter1.RadicalExclusions.ModelReduction.FullSieve
open SourceInterface
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)

include h hn
omit [CharP F 2] in
/-- The whole commutator core is normalized in the original join. -/
theorem join_normalizes_core : (K ⊔ R : Subgroup G) ≤ normalizer ((msQ K R) : Set G) := by
  rw [←commutator_map_eq_msQ]
  let := component_normal h hn
  have hnQ : (⁅pCore 2 (K ⊔ R : Subgroup G),(K.subgroupOf (K ⊔ R))⁆ : Subgroup (K ⊔ R : Subgroup G)).Normal := inferInstance
  exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp (by
    simpa only [subgroupOf,comap_map_eq_self_of_injective ((K ⊔ R : Subgroup G)).subtype_injective] using hnQ)

omit [CharP F 2] in
/-- The literal center, also for nonabelian Q, is normalized by KR. -/
theorem join_normalizes_center :
    (K ⊔ R : Subgroup G) ≤ normalizer (SourceInterface.centerIn (msQ K R) : Set G) :=
  (join_normalizes_core h hn).trans
    (normalizer_le_normalizer_characteristic_image (msQ K R) (center (msQ K R)))

omit [CharP F 2] in
/-- The literal central omega of Q is normalized by KR. -/
theorem join_normalizes_omegaCenter :
    (K ⊔ R : Subgroup G) ≤ normalizer (SourceInterface.omegaCenterIn (msQ K R) : Set G) :=
  (join_normalizes_core h hn).trans (normalizer_le_normalizer_omegaCenterIn (msQ K R))

omit h hn [Finite G] [Field F] [Finite F] [CharP F 2] in
/-- The initial moved subgroup lies in the central omega of the whole core. -/
theorem initialMoved_le_omegaCenter : initialMoved K R ≤ SourceInterface.omegaCenterIn (msQ K R) := by
  intro x hx
  apply (mem_omegaCenterIn_iff _ _).mpr
  refine ⟨initialMoved_le_msQ hx,
    (centralizer_le msQ_le_joinCore) (initialMoved_centralizes_joinCore hx),?_⟩
  have hh : x ∈ Subgroup.omegaCenterIn ((K ⊔ R).pCoreIn 2) :=
    initialOmega_eq (K := K) (R := R) ▸ initialMoved_le_omega hx
  exact ((mem_omegaCenterIn_iff _ _).mp hh).2.2

variable (X : Subgroup G) (hXn : (K ⊔ R : Subgroup G) ≤ normalizer (X : Set G))

/-- Conjugation on an original normalized subgroup, with no carrier change. -/
def sectionAction : (K ⊔ R : Subgroup G) →* MulAut X := X.normalizerMonoidHom.comp (inclusion hXn)

omit h hn [Finite G] [Field F] [Finite F] [CharP F 2] in
theorem sectionAction_apply (g : (K ⊔ R : Subgroup G)) (x : X) :
    (sectionAction X hXn g x : G) = g * (x : G) * (g : G)⁻¹ := by rfl

variable (hUX : initialMoved K R ≤ X) (hXQ : X ≤ centralizer ((msQ K R) : Set G))
include h hn hUX
private theorem sectionAction_kernel_le : (sectionAction X hXn).ker ≤ pCore 2 (K ⊔ R : Subgroup G) := by
  intro g hg
  apply (initialMoved_join_centralizer h hn).le
  intro u hu
  have hu' : (u : G) ∈ initialMoved K R := by
    have hh := mem_map_of_mem ((K ⊔ R : Subgroup G)).subtype hu
    rw [map_commutator,map_subgroupOf_eq_of_le (show K ≤ (K ⊔ R : Subgroup G) from le_sup_left)] at hh
    exact hh
  have he := congrArg (fun a : MulAut X => (a ⟨u,hUX hu'⟩ : G)) hg
  change (g : G) * (u : G) * (g : G)⁻¹ = u at he
  exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp he).symm

omit h hn hUX [Finite G] in
include hXQ in
private theorem sectionAction_commutator :
    ⁅pCore 2 (K ⊔ R : Subgroup G),(K.subgroupOf (K ⊔ R))⁆ ≤ (sectionAction X hXn).ker := by
  intro q hq
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  have hq' : (q : G) ∈ (msQ K R) :=
    (commutator_map_eq_msQ (K := K) (R := R)) ▸ mem_map_of_mem ((K ⊔ R : Subgroup G)).subtype hq
  change (q : G) * (x : G) * (q : G)⁻¹ = x
  rw [hXQ x.property q hq',mul_inv_cancel_right]

include hXn hXQ
/-- On any invariant subgroup containing the initial moved layer and
centralizing Q, the original component image is a perfect central SL₃ cover.
This includes field four and does not assume that Q is abelian. -/
def sectionCover (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) :
    PerfectCentralCovering.Cover ((sectionAction X hXn).comp ((K.subgroupOf (K ⊔ R))).subtype).range SL(3,F) := by
  let := h.component.2.perfect
  exact Matrix.SL3.CommutatorCentralCover.cover (K.subgroupOf (K ⊔ R)) (pCore 2 (K ⊔ R : Subgroup G))
    (joinQuotientEquiv e) (sectionAction X hXn)
    (pCore_subnormal_eq_comap 2 h.component.2.subnormal).symm
    (sectionAction_kernel_le h hn X hXn hUX)
    (sectionAction_commutator X hXn hXQ)

/-- The central cover retains the original quotient marking on every
component representative, including over the exceptional field four. -/
theorem sectionCover_apply (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (k : K.subgroupOf (K ⊔ R)) :
    (sectionCover h hn X hXn hUX hXQ e).toMonoidHom
      (((sectionAction X hXn).comp (K.subgroupOf (K ⊔ R)).subtype).rangeRestrict k) =
        e (QuotientGroup.mk' (pCore 2 K) ⟨k,k.property⟩) := by
  let := h.component.2.perfect
  exact Matrix.SL3.CommutatorCentralCover.cover_apply (F := F) _ _ _ _ _ _ _ k

/-- The entire central section descends to the original full SL₃ marking
outside field four, with literal conjugation on every component element. -/
theorem exists_sectionAction (h4 : n ≠ 2) (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) :
    ∃ b : SL(3,F) →* MulAut X, Function.Injective b ∧
      ∀ (k : K) (x : X), (b (linearThreeActor e k) x : G) =
        k * (x : G) * (k : G)⁻¹ := by
  let := h.component.2.perfect
  have hq2 : Nat.card F ≠ 2 := by
    rw [h.field_card]
    have hh : 2^1 < 2^n := Nat.pow_lt_pow_right (by decide) hn
    omega
  have hq4 : Nat.card F ≠ 4 := by
    rw [h.field_card]
    have hh : 2^2 < 2^n := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  obtain ⟨b,hb,he⟩ := Matrix.SL3.CommutatorCentralCover.exists_descended_action
    (K.subgroupOf (K ⊔ R)) (pCore 2 (K ⊔ R : Subgroup G)) (joinQuotientEquiv e) (sectionAction X hXn)
    (pCore_subnormal_eq_comap 2 h.component.2.subnormal).symm
    (sectionAction_kernel_le h hn X hXn hUX)
    (sectionAction_commutator X hXn hXQ) hq2 hq4
  refine ⟨b,hb,?_⟩
  intro k x
  let l : (K.subgroupOf (K ⊔ R)) := ⟨⟨k,mem_sup_left k.property⟩,k.property⟩
  have hh := congrArg (fun a : MulAut X => (a x : G)) (he l)
  exact hh

omit h hn hXn hUX hXQ

omit [Finite G] in
private theorem center_centralizes : SourceInterface.centerIn (msQ K R) ≤ centralizer ((msQ K R) : Set G) := by
  rintro x ⟨z,hz,rfl⟩ y hy
  exact congrArg (msQ K R).subtype (mem_center_iff.mp hz ⟨y,hy⟩)

include h hn in
/-- The actual whole center admits a faithful marked action even when Q
is nonabelian; no natural section is assumed. -/
theorem exists_centerAction (h4 : n ≠ 2) (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) :
    ∃ b : SL(3,F) →* MulAut (SourceInterface.centerIn (msQ K R)), Function.Injective b ∧
      ∀ (k : K) (x : SourceInterface.centerIn (msQ K R)),
        (b (linearThreeActor e k) x : G) = k * (x : G) * (k : G)⁻¹ :=
  exists_sectionAction h hn _ (join_normalizes_center h hn)
    initialMoved_le_core_center center_centralizes h4 e

include h hn in
/-- The central omega of the whole core has a faithful marked SL₃ action,
without abelianity of Q or a whole-section recognition premise. -/
theorem exists_omegaCenterAction (h4 : n ≠ 2) (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) :
    ∃ b : SL(3,F) →* MulAut (SourceInterface.omegaCenterIn (msQ K R)), Function.Injective b ∧
      ∀ (k : K) (x : SourceInterface.omegaCenterIn (msQ K R)),
        (b (linearThreeActor e k) x : G) = k * (x : G) * (k : G)⁻¹ :=
  exists_sectionAction h hn _ (join_normalizes_omegaCenter h hn)
    initialMoved_le_omegaCenter
    (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1) h4 e


include h hn in
omit [CharP F 2] in
private theorem initialMoved_idempotent : ⁅initialMoved K R,K⁆ = initialMoved K R := by
  apply commutator_isPPerfect_idempotent K (initialOmega K R) (component_twoPerfect h hn)
  · rw [initialOmega_eq]
    exact IsElementaryAbelian.isPGroup 2 _
  · rw [initialOmega_eq]
    exact (le_sup_left : K ≤ (K ⊔ R : Subgroup G)).trans (((K ⊔ R : Subgroup G)).le_normalizer.trans
      ((normalizer_le_normalizer_characteristic_image (K ⊔ R : Subgroup G) (pCore 2 (K ⊔ R : Subgroup G))).trans
        (normalizer_le_normalizer_omegaCenterIn ((K ⊔ R : Subgroup G).pCoreIn 2))))

include h hn in
/-- The fourth row's actual moved center also retains the original SL₃
marking, without assuming its natural-module identification. -/
theorem exists_centerCommutatorAction (h4 : n ≠ 2)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) :
    ∃ b : SL(3,F) →* MulAut (⁅SourceInterface.centerIn (msQ K R),K⁆ : Subgroup G),
      Function.Injective b ∧
      ∀ (k : K) (x : (⁅SourceInterface.centerIn (msQ K R),K⁆ : Subgroup G)),
        (b (linearThreeActor e k) x : G) = k * (x : G) * (k : G)⁻¹ := by
  have hJK : (K ⊔ R : Subgroup G) ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show K ≤ (K ⊔ R : Subgroup G) from le_sup_left)).mp
      (component_normal h hn)
  have hJU : (K ⊔ R : Subgroup G) ≤ normalizer (⁅SourceInterface.centerIn (msQ K R),K⁆ : Subgroup G) := by
    intro j hj
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (join_normalizes_center h hn hj),
      mem_normalizer_iff_map_conj_eq.mp (hJK hj)]
  have hUZ : ⁅SourceInterface.centerIn (msQ K R),K⁆ ≤ SourceInterface.centerIn (msQ K R) :=
    le_normalizer_iff_commutator_le_left.mp
      ((le_sup_left : K ≤ (K ⊔ R : Subgroup G)).trans (join_normalizes_center h hn))
  have hIU : initialMoved K R ≤ ⁅SourceInterface.centerIn (msQ K R),K⁆ := by
    rw [←initialMoved_idempotent h hn]
    exact commutator_mono initialMoved_le_core_center le_rfl
  exact exists_sectionAction h hn _ hJU hIU (hUZ.trans center_centralizes) h4 e

include h hn in
/-- In the nonabelian branches too, the entire center centralizes the
intrinsic component two-core outside field four. -/
theorem center_centralizes_componentCore (h4 : n ≠ 2) :
    SourceInterface.centerIn (msQ K R) ≤ centralizer (K.pCoreIn 2 : Set G) := by
  let e := Classical.choice h.model
  obtain ⟨b,_,hb⟩ := exists_centerAction h hn h4 e
  intro x hx y hy
  obtain ⟨k,hk,rfl⟩ := hy
  have he : linearThreeActor e k = 1 := by
    change e (QuotientGroup.mk' (pCore 2 K) k) = 1
    rw [MulEquiv.map_eq_one_iff]
    exact (QuotientGroup.eq_one_iff k).mpr hk
  have hh := hb k ⟨x,hx⟩
  rw [he,map_one] at hh
  exact mul_inv_eq_iff_eq_mul.mp hh.symm

/-- The original whole-core central omega, restricted only to the join carrier. -/
def coreOmegaLayer : Subgroup (K ⊔ R : Subgroup G) := (SourceInterface.omegaCenterIn (msQ K R)).subgroupOf (K ⊔ R : Subgroup G)

omit [Finite G] in
/-- The layer retains the original subgroup and its literal inclusion in KR. -/
theorem coreOmegaLayer_eq : coreOmegaLayer (K := K) (R := R) =
    (SourceInterface.omegaCenterIn (msQ K R)).subgroupOf (K ⊔ R : Subgroup G) := by
  unfold coreOmegaLayer
  rfl

omit [Finite G] in
private theorem omega_le_join : SourceInterface.omegaCenterIn (msQ K R) ≤ (K ⊔ R : Subgroup G) :=
  (map_subtype_le _).trans (msQ_le_joinCore.trans (pCoreIn_le 2 (K ⊔ R : Subgroup G)))

include h hn in
omit [CharP F 2] in
/-- Normality is relative to KR. -/
theorem coreOmegaLayer_normal : (coreOmegaLayer (K := K) (R := R)).Normal :=
  (normal_subgroupOf_iff_le_normalizer omega_le_join).mpr (join_normalizes_omegaCenter h hn)

omit [Finite G] in
/-- The actual central omega is elementary even for nonabelian Q. -/
theorem coreOmegaLayer_elementary : IsElementaryAbelian 2 (coreOmegaLayer (K := K) (R := R)) := by
  let : IsElementaryAbelian 2 (SourceInterface.omegaCenterIn (msQ K R)) :=
    Subgroup.omegaCenterIn_elementary _
  let e := subgroupOfEquivOfLe (omega_le_join (K := K) (R := R))
  exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective

omit [Finite G] in
/-- The whole-core central omega lies in the original join's two-core. -/
theorem coreOmegaLayer_le_core : coreOmegaLayer (K := K) (R := R) ≤ pCore 2 (K ⊔ R : Subgroup G) := by
  rw [← (pCore 2 (K ⊔ R : Subgroup G)).comap_map_eq_self_of_injective ((K ⊔ R : Subgroup G)).subtype_injective]
  exact comap_mono ((map_subtype_le _).trans msQ_le_joinCore)

include h hn in
/-- The centralizer of the whole-core central omega lies in the original
two-core, including at field four and for nonabelian Q. -/
theorem coreOmegaLayer_centralizer_le :
    centralizer (coreOmegaLayer (K := K) (R := R) : Set (K ⊔ R : Subgroup G)) ≤ pCore 2 (K ⊔ R : Subgroup G) := by
  apply le_trans _ (initialMoved_join_centralizer h hn).le
  apply centralizer_le
  intro u hu
  apply initialMoved_le_omegaCenter
  have hh := mem_map_of_mem ((K ⊔ R : Subgroup G)).subtype hu
  rw [map_commutator,map_subgroupOf_eq_of_le (show K ≤ (K ⊔ R : Subgroup G) from le_sup_left)] at hh
  exact hh

include h hn

/-- The faithful action on the central omega uses its literal centralizer
quotient; no recognition of a natural module is assumed. -/
def coreOmegaRepresentation :
    letI := coreOmegaLayer_normal h hn
    letI := coreOmegaLayer_elementary (K := K) (R := R)
    Representation (ZMod 2)
      ((K ⊔ R : Subgroup G) ⧸ centralizer (coreOmegaLayer (K := K) (R := R) : Set (K ⊔ R : Subgroup G)))
      (Additive (coreOmegaLayer (K := K) (R := R))) := by
  let := coreOmegaLayer_normal h hn
  let := coreOmegaLayer_elementary (K := K) (R := R)
  exact NormalElementaryQuotient.representation (coreOmegaLayer (K := K) (R := R))
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

omit [CharP F 2] in
/-- Equation for the literal quotient action, for transporting offender witnesses. -/
theorem coreOmegaRepresentation_eq :
    letI := coreOmegaLayer_normal h hn
    letI := coreOmegaLayer_elementary (K := K) (R := R)
    coreOmegaRepresentation h hn =
      NormalElementaryQuotient.representation (coreOmegaLayer (K := K) (R := R))
        (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) := by
  unfold coreOmegaRepresentation
  rfl

omit [CharP F 2] in
/-- The central-omega action is faithful on the exact centralizer quotient. -/
theorem coreOmegaRepresentation_injective :
    letI := coreOmegaLayer_normal h hn
    letI := coreOmegaLayer_elementary (K := K) (R := R)
    Function.Injective (coreOmegaRepresentation h hn) := by
  let := coreOmegaLayer_normal h hn
  let := coreOmegaLayer_elementary (K := K) (R := R)
  unfold coreOmegaRepresentation
  exact NormalElementaryQuotient.representation_injective _ _ _ _

/-- MS3 supplies an offender on the entire central omega of Q, including
the nonabelian branches and field four. -/
theorem coreOmega_isFF :
    letI := coreOmegaLayer_normal h hn
    letI := coreOmegaLayer_elementary (K := K) (R := R)
    Representation.BinaryOffender.IsFFModule (coreOmegaRepresentation h hn) := by
  let := coreOmegaLayer_normal h hn
  let := coreOmegaLayer_elementary (K := K) (R := R)
  unfold coreOmegaRepresentation
  apply NormalElementaryQuotient.isFFModule_of_thompson_not_le _ _ _ _ (R.subgroupOf (K ⊔ R : Subgroup G))
    (coreOmegaLayer_le_core.trans (join_oddIndex h hn).twoCore_le)
  rw [QuotientGroup.ker_mk']
  intro he
  exact (join_characteristic h).thompson_not_le_core
    (join_oddIndex h hn).isPGroup (radical_ne_bot h hn) (join_oddIndex h hn).twoCore_le
    (he.trans (coreOmegaLayer_centralizer_le h hn))

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.CentralSections
