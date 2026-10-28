module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.CentralSections
public import Theory.Representation.FrattiniAction
public import Theory.Representation.BinaryOffender.ConjugationGeneration

/-!
# The whole Frattini section of a nonbinary linear-three MS core

Let Q=[O₂(KR),K]. Burnside's Frattini automorphism-kernel theorem and the
proved bound C_KR(Q)≤O₂(KR) put the kernel of the literal action on Q/Φ(Q)
inside O₂(KR). Inner conjugation by Q is trivial on this elementary quotient.
Thus its component image is a perfect central cover of the original full
SL₃, including at field four. The covering map preserves the supplied marking.

Outside field four, the ordinary scalar-cover theorem removes the covering
kernel. This gives a faithful binary SL₃ representation on the entire Q/Φ(Q),
with literal conjugation and full component-commutator generation. In particular
[O₂(K),Q]≤Φ(Q), without assuming Q abelian. The original Chapter4 nonblock and
Chapter11 point configurations use these results.

These are reductions for the source sections, not their natural/dual recognition.
The exceptional covering kernel, whole central/Frattini module models, and
Sylow radical inequalities in C.1.34 remain open.
Source: Aschbacher--Smith C.1.34, printed pp.136--137, I.1.3, printed p.407,
and original4.3.8--10 and11.1.5; Burnside's basis-kernel theorem is proved in
Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.FrattiniSections
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "L" => K.subgroupOf (K ⊔ R)
local notation "N" => pCore 2 (K ⊔ R : Subgroup G)
local notation "Q" => msQ K R

/-- Conjugation on the actual commutator core. -/
def coreAction : J →* MulAut Q :=
  (Q).normalizerMonoidHom.comp (inclusion (CentralSections.join_normalizes_core h hn))

/-- The canonical action on the entire original Frattini quotient. -/
def frattiniAction : J →* MulAut (Q ⧸ frattini Q) :=
  (quotientAut (frattini Q)).comp (coreAction h hn)

omit [CharP F 2] in
/-- The action uses the literal conjugation on the original quotient. -/
theorem frattiniAction_apply (g : J) (x : Q) :
    frattiniAction h hn g (QuotientGroup.mk' (frattini Q) x) =
      QuotientGroup.mk' (frattini Q)
        ⟨(g : G) * (x : G) * (g : G)⁻¹,
          (CentralSections.join_normalizes_core h hn g.property x).mp x.property⟩ := by
  change quotientAut (frattini Q) (coreAction h hn g) _ = _
  rw [quotientAut_apply_mk]
  rfl

include h hn
private theorem coreAction_kernel_le : (coreAction h hn).ker ≤ N := by
  intro g hg
  apply wholeCore_join_centralizer_le h hn
  intro q hq
  have hq' : (q : G) ∈ Q :=
    (commutator_map_eq_msQ (K := K) (R := R)) ▸ mem_map_of_mem (J).subtype hq
  have he := congrArg (fun a : MulAut Q => (a ⟨q,hq'⟩ : G)) hg
  change (g : G) * (q : G) * (g : G)⁻¹ = q at he
  exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp he).symm

omit h hn [Finite G] [Field F] [Finite F] [CharP F 2] in
private theorem core_isPGroup : IsPGroup 2 Q :=
  (pCore_isPGroup.map (J).subtype).to_le msQ_le_joinCore

/-- The whole Frattini action has only a normal two-group kernel. -/
theorem frattiniAction_kernel_le : (frattiniAction h hn).ker ≤ N := by
  have hp : IsPGroup 2 (frattiniAction h hn).ker :=
    (isPGroup_quotientAut_frattini_kernel (core_isPGroup (K := K) (R := R))).comap_of_ker_isPGroup
      (coreAction h hn) (pCore_isPGroup.to_le (coreAction_kernel_le h hn))
  exact le_sSup ⟨inferInstance,hp⟩

omit [CharP F 2] in
/-- The core itself acts by inner automorphisms, trivial modulo Frattini. -/
theorem core_le_frattiniAction_kernel :
    ⁅N,L⁆ ≤ (frattiniAction h hn).ker := by
  intro q hq
  have hq' : (q : G) ∈ Q :=
    (commutator_map_eq_msQ (K := K) (R := R)) ▸ mem_map_of_mem (J).subtype hq
  have he : coreAction h hn q = MulAut.conj (⟨q,hq'⟩ : Q) := by
    ext x
    rfl
  change quotientAut (frattini Q) (coreAction h hn q) = 1
  rw [he]
  exact Representation.FrattiniAction.quotientAut_conj_eq_one (core_isPGroup (K := K) (R := R)) _

/-- The actual component image covers the full marked SL₃ at every nonbinary field. -/
def frattiniCover (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) :
    PerfectCentralCovering.Cover ((frattiniAction h hn).comp (L).subtype).range SL(3,F) := by
  let := h.component.2.perfect
  exact Matrix.SL3.CommutatorCentralCover.cover L N (joinQuotientEquiv e)
    (frattiniAction h hn)
    (pCore_subnormal_eq_comap 2 h.component.2.subnormal).symm
    (frattiniAction_kernel_le h hn) (core_le_frattiniAction_kernel h hn)

/-- Away from field four the action descends faithfully to the supplied full quotient. -/
theorem exists_frattiniAction (h4 : n ≠ 2) (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) :
    ∃ b : SL(3,F) →* MulAut (Q ⧸ frattini Q), Function.Injective b ∧
      ∀ k : K, b (linearThreeActor e k) =
        frattiniAction h hn ⟨k,mem_sup_left k.property⟩ := by
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
    L N (joinQuotientEquiv e) (frattiniAction h hn)
    (pCore_subnormal_eq_comap 2 h.component.2.subnormal).symm
    (frattiniAction_kernel_le h hn) (core_le_frattiniAction_kernel h hn) hq2 hq4
  exact ⟨b,hb,fun k => he ⟨⟨k,mem_sup_left k.property⟩,k.property⟩⟩

omit h hn [Finite G] [Field F] [Finite F] [CharP F 2] in
/-- The quotient is the actual Frattini section occurring in C.1.34. -/
theorem frattiniIn_subgroupOf : (frattiniIn Q).subgroupOf Q = frattini Q := by
  exact (frattini Q).comap_map_eq_self_of_injective (Q).subtype_injective

omit h hn [Field F] [Finite F] [CharP F 2] in
/-- The entire Frattini quotient is an elementary two-group. -/
theorem frattini_elementary : IsElementaryAbelian 2 (Q ⧸ frattini Q) := by
  let : Fact (IsPGroup 2 Q) := ⟨core_isPGroup⟩
  exact isElementaryAbelian_quotient_frattini

/-- The covering component is quasisimple also at field four. -/
theorem frattini_component_quasisimple :
    IsQuasisimple ((frattiniAction h hn).comp (L).subtype).range := by
  let : IsQuasisimple SL(3,F) := {
    toIsPerfect := Atlas.sl_perfect 3 (by decide)
    simple := Atlas.psl_simple_high_rank 3 (by decide) }
  exact (frattiniCover h hn (Classical.choice h.model)).isQuasisimple

/-- The specified marking survives on the whole Frattini representation,
which is generated by its component displacements. -/
theorem exists_frattiniRepresentation (h4 : n ≠ 2) (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) :
    letI := frattini_elementary (K := K) (R := R)
    ∃ ρ : Representation (ZMod 2) SL(3,F) (Additive (Q ⧸ frattini Q)),
      Function.Injective ρ ∧
      (∀ (k : K) (x x' : Q), (x' : G) = k * (x : G) * (k : G)⁻¹ →
        ρ (linearThreeActor e k) (Additive.ofMul (QuotientGroup.mk' (frattini Q) x)) =
          Additive.ofMul (QuotientGroup.mk' (frattini Q) x')) ∧
      BinaryOffender.subspaceCommutator ρ ⊤ ⊤ = ⊤ := by
  let := frattini_elementary (K := K) (R := R)
  obtain ⟨b,hb,he⟩ := exists_frattiniAction h hn h4 e
  let ρ := Representation.FrattiniAction.ofAutomorphismHom b
  have hρ (k : K) (x : Q) :
      ρ (linearThreeActor e k) (Additive.ofMul (QuotientGroup.mk' (frattini Q) x)) =
        Additive.ofMul (frattiniAction h hn ⟨k,mem_sup_left k.property⟩
          (QuotientGroup.mk' (frattini Q) x)) := by
    change Additive.ofMul (b (linearThreeActor e k) _) = _
    rw [he]
    rfl
  refine ⟨ρ,?_,?_,?_⟩
  · intro a c hac
    apply hb
    ext v
    exact congrArg (fun z : Module.End (ZMod 2) (Additive (Q ⧸ frattini Q)) =>
      (z (Additive.ofMul v)).toMul) hac
  · intro k x x' hx
    rw [hρ,frattiniAction_apply]
    exact congrArg (fun y => Additive.ofMul (QuotientGroup.mk' (frattini Q) y))
      (Subtype.ext hx.symm)
  · have hnQ : K ≤ normalizer (Q : Set G) :=
      (le_sup_left : K ≤ K ⊔ R).trans (CentralSections.join_normalizes_core h hn)
    have hh := BinaryOffender.commutator_eq_top_of_conjugation ρ Q K hnQ
      (linearThreeActor e) (QuotientGroup.mk' (frattini Q))
      (QuotientGroup.mk'_surjective _)
      (fun k x => by rw [hρ,frattiniAction_apply])
      (by rw [commutator_comm]; exact msQ_idempotent h hn)
    have he : (linearThreeActor e).range = ⊤ := MonoidHom.range_eq_top.mpr
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
    rwa [he] at hh

/-- Outside field four the intrinsic component core acts trivially on the
whole Frattini quotient, even when Q is nonabelian. -/
theorem componentCore_commutator_le_frattini (h4 : n ≠ 2) :
    ⁅K.pCoreIn 2,Q⁆ ≤ frattiniIn Q := by
  obtain ⟨e⟩ := h.model
  obtain ⟨b,_,he⟩ := exists_frattiniAction h hn h4 e
  apply commutator_le.mpr
  rintro a ⟨k,hk,rfl⟩ x hx
  let xQ : Q := ⟨x,hx⟩
  let x' : Q := ⟨(k : G) * x * (k : G)⁻¹,
    (CentralSections.join_normalizes_core h hn (mem_sup_left k.property) x).mp hx⟩
  have hk1 : linearThreeActor e k = 1 := by
    change e (QuotientGroup.mk' (pCore 2 K) k) = 1
    exact (congrArg e ((QuotientGroup.eq_one_iff k).mpr hk)).trans e.map_one
  have htriv : frattiniAction h hn ⟨k,mem_sup_left k.property⟩ = 1 := by
    rw [←he,hk1,map_one]
  have hx' : QuotientGroup.mk' (frattini Q) x' = QuotientGroup.mk' (frattini Q) xQ := by
    rw [←frattiniAction_apply h hn ⟨k,mem_sup_left k.property⟩ xQ,htriv]
    rfl
  have hp : x' * xQ⁻¹ ∈ frattini Q := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (frattini Q) (x' * xQ⁻¹) = 1
    rw [map_mul,map_inv,hx',mul_inv_cancel]
  exact ⟨x' * xQ⁻¹,hp,rfl⟩

/-- The central covering map retains the original full SL₃ marking. -/
theorem frattiniCover_apply (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (k : L) :
    (frattiniCover h hn e).toMonoidHom
      (((frattiniAction h hn).comp (L).subtype).rangeRestrict k) =
        e (QuotientGroup.mk' (pCore 2 K) ⟨k,k.property⟩) := by
  let := h.component.2.perfect
  exact Matrix.SL3.CommutatorCentralCover.cover_apply L N (joinQuotientEquiv e)
    (frattiniAction h hn)
    (pCore_subnormal_eq_comap 2 h.component.2.subnormal).symm
    (frattiniAction_kernel_le h hn) (core_le_frattiniAction_kernel h hn) k

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.FrattiniSections
