module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.MarkedInitial
public import Theory.GroupTheory.MSCharacteristicAbelianCommutator
public import Theory.ElementaryAbelian.Injective

/-!
# The actual nonbinary MS core: centralizers, exponent and offenders

The split initial omega layer has exactly O₂(KR) as the centralizer of
its moved subgroup. Indeed a component element fixing the moved subgroup
also fixes the complementary component-fixed subgroup. The quasisimple
normal-kernel bound then removes every remaining kernel element. Since
that moved subgroup lies in msQ, the centralizer of the entire msQ also
lies in O₂(KR), including in the nonabelian branch.

In the abelian branch, the genuine MS3 condition and the full quasisimple
component quotient force msQ to have exponent two. The literal action of
KR/C_KR(msQ) on this entire elementary core is faithful. MS3 forces a
maximum elementary subgroup of R to escape its kernel, providing an
FF-offender on the whole core. All quotient and subgroup maps remain the
original ones, and the scalar center of SL₃(4) is retained.

This supplies the elementary and whole-core-offender inputs for further
reconstruction. Descent to the specified full SL₃ action, its natural or
doubled-natural recognition, the nonabelian central/Frattini sections,
and the Sylow radical inequalities remain unproved. No C.1.34 classification
or original-ambient fixed-factor centrality is asserted.

Source: Aschbacher--Smith C.1.31--34, printed pp.135--137, and original
4.3.8--10, pp.616--617; the MS3/Thompson argument of B.2.4 and B.2.10.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "L" => (K.subgroupOf (K ⊔ R))
local notation "T" => (R.subgroupOf (K ⊔ R))
local notation "E" => (centralOmegaLayer K R)
local notation "U" => (⁅centralOmegaLayer K R,K.subgroupOf (K ⊔ R)⁆ : Subgroup (K ⊔ R : Subgroup G))
local notation "Q" => (⁅pCore 2 (K ⊔ R : Subgroup G),K.subgroupOf (K ⊔ R)⁆ : Subgroup (K ⊔ R : Subgroup G))

include h hn

/-- Abelianity of the literal MS core already forces exponent two. -/
theorem abelian_msQ_elementary (hc : IsMulCommutative (msQ K R)) :
    IsElementaryAbelian 2 (msQ K R) := by
  let := component_normal h hn
  let := h.component.2.perfect
  let := join_quotient_quasisimple h
  let q := QuotientGroup.mk' (pCore 2 J)
  let B := (L).map q
  let : B.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv h.component.2)
  have hgen : L ⊔ T = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hF : generalizedFitting (J ⧸ pCore 2 J) = B :=
    generalizedFitting_eq_of_quasisimple_two_quotient B
      (isPGroup_quotient_of_sup_eq_top B ((T).map q)
        ((join_oddIndex h hn).isPGroup.map q) (by
          rw [← Subgroup.map_sup,hgen,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]))
      (pCore_quotient_pCore_eq_bot 2)
  have hcomm : IsMulCommutative Q := by
    apply isMulCommutative_iff.mpr
    intro x y
    apply Subtype.ext
    apply Subtype.ext
    have hx : ((x : J) : G) ∈ msQ K R := (commutator_map_eq_msQ (K := K) (R := R)) ▸ mem_map_of_mem (J).subtype x.property
    have hy : ((y : J) : G) ∈ msQ K R := (commutator_map_eq_msQ (K := K) (R := R)) ▸ mem_map_of_mem (J).subtype y.property
    exact congrArg (fun z : msQ K R => (z : G))
      (hc.is_comm.comm (⟨_,hx⟩ : msQ K R) ⟨_,hy⟩)
  let := hcomm
  let : IsElementaryAbelian 2 Q := MSAbelianCommutator.elementary_of_abelian L T
    (join_oddIndex h hn).isPGroup (join_oddIndex h hn).twoCore_le hgen
    (fun C hC hN => by
      let := hC
      exact (join_characteristic h).eq_bot_of_normal C hN) hF
  rw [← commutator_map_eq_msQ]
  exact IsElementaryAbelian.map (J).subtype

variable [CharP F 2]

private theorem component_moved_centralizer (k : J) (hk : k ∈ L)
    (hu : k ∈ centralizer (U : Set J)) : k ∈ centralOmegaKernel K R := by
  have hmap : (U).map (J).subtype = initialMoved K R := by
    rw [map_commutator,map_subgroupOf_eq_of_le (show K ≤ K ⊔ R from le_sup_left)]
    rfl
  have hku : (k : G) ∈ centralizer (initialMoved K R : Set G) := by
    rw [← hmap]
    rintro x ⟨u,hu',rfl⟩
    exact congrArg (J).subtype (hu u hu')
  have hz : initialOmega K R ≤ centralizer (zpowers (k : G) : Set G) := by
    rw [← (initialMoved_split h hn).1]
    exact sup_le (le_centralizer_iff.mp (zpowers_le.mpr hku))
      (inf_le_right.trans (centralizer_le (zpowers_le.mpr hk)))
  have hce := (le_centralizer_iff.mp hz) (mem_zpowers (k : G))
  intro e he
  exact Subtype.ext (hce e (mem_map_of_mem (J).subtype he))

/-- Moving the central omega retains its exact two-core centralizer. -/
theorem initialMoved_join_centralizer : centralizer (U : Set J) = pCore 2 J := by
  let := component_normal h hn
  let := join_quotient_quasisimple h
  let C := centralizer (U : Set J)
  let : C.Normal := inferInstance
  have hNC : pCore 2 J ≤ C :=
    core_le_centralOmegaKernel.trans (centralizer_le (commutator_le_left E L))
  have hnot : ¬ L ≤ C := by
    intro hc
    apply component_not_le_centralOmegaKernel h hn
    intro k hk
    exact component_moved_centralizer h hn k hk (hc hk)
  have hbound : C ≤ pCore 2 J ⊔ L :=
    (QuasisimpleKernel.normal_kernel_structure L T C h.component.2
      (join_oddIndex h hn).isPGroup
      (by rw [← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]) hNC hnot).1.trans
        (sup_le_sup le_rfl (map_subtype_le _))
  apply le_antisymm _ hNC
  intro x hx
  obtain ⟨a,ha,k,hk,rfl⟩ := mem_sup_of_normal_left.mp (hbound hx)
  have hkC : k ∈ C := by
    have hh := C.mul_mem (C.inv_mem (hNC ha)) hx
    simpa only [inv_mul_cancel_left] using hh
  have hkN : k ∈ pCore 2 J :=
    (centralOmega_kernel_eq_core h hn).le (component_moved_centralizer h hn k hk hkC)
  exact (pCore 2 J).mul_mem ha hkN

/-- The whole core centralizer is contained in the original two-core. -/
theorem wholeCore_join_centralizer_le : centralizer (Q : Set J) ≤ pCore 2 J := by
  have hu : U ≤ Q := commutator_mono (show E ≤ pCore 2 J from map_subtype_le _) le_rfl
  exact (centralizer_le hu).trans_eq (initialMoved_join_centralizer h hn)

/-- The original ambient statement of the whole-core centralizer bound. -/
theorem msQ_centralizer_le_core :
    (K ⊔ R) ⊓ centralizer (msQ K R : Set G) ≤ (K ⊔ R).pCoreIn 2 := by
  intro x hx
  apply mem_map_of_mem (J).subtype (x := ⟨x,hx.1⟩)
  apply wholeCore_join_centralizer_le h hn
  intro d hd
  apply Subtype.ext
  exact hx.2 d ((commutator_map_eq_msQ (K := K) (R := R)) ▸ mem_map_of_mem (J).subtype hd)

omit [CharP F 2] in
/-- The same exponent-two assertion on the literal join carrier. -/
theorem abelian_joinCore_elementary (hc : IsMulCommutative (msQ K R)) :
    IsElementaryAbelian 2 Q := by
  let : IsElementaryAbelian 2 (msQ K R) := abelian_msQ_elementary h hn hc
  let e := ((Q).equivMapOfInjective (J).subtype (J).subtype_injective).trans
    (MulEquiv.subgroupCongr commutator_map_eq_msQ)
  exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective

/-- The literal whole-core representation, under the abelian branch hypothesis. -/
def wholeCoreRepresentation (hc : IsMulCommutative (msQ K R)) :
    letI := component_normal h hn
    letI := abelian_joinCore_elementary h hn hc
    Representation (ZMod 2) (J ⧸ centralizer (Q : Set J)) (Additive Q) := by
  let := component_normal h hn
  let := abelian_joinCore_elementary h hn hc
  exact NormalElementaryQuotient.representation Q (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

omit [CharP F 2] in
/-- Equation for transporting the actual maximum elementary offender witnesses. -/
theorem wholeCoreRepresentation_eq (hc : IsMulCommutative (msQ K R)) :
    letI := component_normal h hn
    letI := abelian_joinCore_elementary h hn hc
    wholeCoreRepresentation h hn hc =
      NormalElementaryQuotient.representation Q (QuotientGroup.mk' _)
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) := by
  unfold wholeCoreRepresentation
  rfl

omit [CharP F 2] in
/-- Whole-core coordinates retain literal conjugation by every join element. -/
theorem wholeCoreRepresentation_apply (hc : IsMulCommutative (msQ K R))
    (j : J) (v : Additive Q) :
    letI := component_normal h hn
    letI := abelian_joinCore_elementary h hn hc
    (((wholeCoreRepresentation h hn hc) (QuotientGroup.mk' _ j) v).toMul : J) =
      j * (v.toMul : J) * j⁻¹ := by
  let := component_normal h hn
  let := abelian_joinCore_elementary h hn hc
  unfold wholeCoreRepresentation
  exact NormalElementaryQuotient.representation_apply Q (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) j v

omit [CharP F 2] in
/-- The whole-core centralizer quotient acts faithfully. -/
theorem wholeCoreRepresentation_injective (hc : IsMulCommutative (msQ K R)) :
    letI := component_normal h hn
    letI := abelian_joinCore_elementary h hn hc
    Function.Injective (wholeCoreRepresentation h hn hc) := by
  let := component_normal h hn
  let := abelian_joinCore_elementary h hn hc
  unfold wholeCoreRepresentation
  exact NormalElementaryQuotient.representation_injective Q (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

/-- MS3 supplies an FF-offender on the entire abelian core, through its
actual centralizer quotient. The initial omega is not substituted for the core. -/
theorem wholeCore_isFF (hc : IsMulCommutative (msQ K R)) :
    letI := component_normal h hn
    letI := abelian_joinCore_elementary h hn hc
    IsFFModule (wholeCoreRepresentation h hn hc) := by
  let := component_normal h hn
  let := abelian_joinCore_elementary h hn hc
  unfold wholeCoreRepresentation
  apply NormalElementaryQuotient.isFFModule_of_thompson_not_le Q _ _ _ T
    ((commutator_le_left _ _).trans (join_oddIndex h hn).twoCore_le)
  rw [QuotientGroup.ker_mk']
  intro he
  exact (join_characteristic h).thompson_not_le_core
    (join_oddIndex h hn).isPGroup (radical_ne_bot h hn) (join_oddIndex h hn).twoCore_le
    (he.trans (wholeCore_join_centralizer_le h hn))

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource
