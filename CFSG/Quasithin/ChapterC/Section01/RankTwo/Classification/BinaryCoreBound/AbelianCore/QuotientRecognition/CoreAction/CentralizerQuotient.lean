module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.ReducedFF

/-!
# The actual ambient FF-action on an elementary binary MS core

Write D=[O₂(J),L]. The component acts nontrivially on D because [D,L]=D≠1.
Simplicity of L/O₂(L) and perfectness show C_L(D)≤O₂(L). The image of
C_J(D) in Aut(L/O₂(L)) therefore centralizes all inner automorphisms;
centerlessness gives C_J(D)≤O₂(J).

Consequently every maximum elementary subgroup E of R outside O₂(J)
acts nontrivially on D. If D is elementary, maximum-elementary counting
constructs a faithful FF-representation of the actual ambient conjugation
image J/C_J(D), with its representative formula and full generation by
the component's displacements. The elementary hypothesis remains explicit.
If D is abelian, the images of O₂(J) and L commute in this action group.

This is a reduction toward the whole-core SL₃(2) action, not its assertion.
Exponent two, centrality of the intrinsic O₂(L) action, and transfer of an
offender to that SL₃(2) action remain separate local proof obligations.
In particular, C_J(D) is not identified with O₂(J), and D is not identified
with the central omega module used to choose E.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.31–34,
printed pp.135–137; the maximum-elementary counting argument of B.2.4.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R)

include h in
/-- Full commutator generation and nontriviality exclude a trivial component action. -/
theorem Input.component_not_centralizes_core :
    ¬ L ≤ centralizer (commutatorCore L : Set J) := by
  intro hz
  have hbot := commutator_eq_bot_iff_le_centralizer.mpr hz
  rw [commutator_comm, h.commutatorCore_idempotent] at hbot
  exact h.commutatorCore_ne_bot hbot

include h in
/-- The kernel of the component action lies in its intrinsic two-core. -/
theorem Input.component_core_centralizer_le :
    (centralizer (commutatorCore L : Set J)).subgroupOf L ≤ pCore 2 L := by
  let := h.component_normal
  let C := (centralizer (commutatorCore L : Set J)).subgroupOf L
  let q := QuotientGroup.mk' (pCore 2 L)
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (L ⧸ pCore 2 L) :=
    (h.quotientEquiv.trans Matrix.PSL3Two.equiv).isSimpleGroup
  have hnorm : (C.map q).Normal :=
    (inferInstance : C.Normal).map q (QuotientGroup.mk'_surjective _)
  rcases hnorm.eq_bot_or_eq_top with hc | hc
  · simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff C).mp hc
  · have hsup : C ⊔ pCore 2 L = ⊤ := by
      have hh := congrArg (fun K => K.comap q) hc
      simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh
    have hp : IsPGroup 2 (L ⧸ C) :=
      isPGroup_quotient_of_sup_eq_top C (pCore 2 L) pCore_isPGroup hsup
    let := h.component.perfect
    have hs : Subsingleton (L ⧸ C) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (L ⧸ C) hp.isNilpotent
    have hCt : C = ⊤ := by
      apply eq_top_iff.mpr
      intro l _
      exact (QuotientGroup.eq_one_iff l).mp (Subsingleton.elim _ _)
    exact (h.component_not_centralizes_core (subgroupOf_eq_top.mp hCt)).elim

include h in
/-- The centralizer of the whole core lies in the ambient two-core. -/
theorem Input.core_centralizer_le :
    centralizer (commutatorCore L : Set J) ≤ pCore 2 J := by
  let := h.component_normal
  let C := centralizer (commutatorCore L : Set J)
  have hCL : C ⊓ L ≤ pCore 2 J := by
    intro x hx
    have hxL : (⟨x, hx.2⟩ : L) ∈ pCore 2 L :=
      h.component_core_centralizer_le hx.1
    exact (h.componentCore_eq_inf.le (mem_map_of_mem L.subtype hxL)).1
  have hk : ⁅C, L⁆ ≤ h.quotientAction.ker := by
    rw [h.quotientAction_kernel]
    exact (commutator_le_inf C L).trans hCL
  have hi : L.map h.quotientAction = MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
    apply le_antisymm
    · rintro a ⟨l, hl, rfl⟩
      exact ⟨QuotientGroup.mk' (pCore 2 L) ⟨l, hl⟩,
        (h.quotientAction_component ⟨l, hl⟩).symm⟩
    · rintro a ⟨x, rfl⟩
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
      exact ⟨l, l.property, h.quotientAction_component l⟩
  have hcomm : ⁅C.map h.quotientAction, MulAut.innerSubgroup (L ⧸ pCore 2 L)⁆ = ⊥ := by
    rw [← hi, ← map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr hk
  have hzero : C.map h.quotientAction = ⊥ := by
    apply le_bot_iff.mp
    exact (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      (MulAut.centralizer_innerSubgroup_eq_bot h.quotient_center).le
  have hle := (Subgroup.map_eq_bot_iff C).mp hzero
  rwa [h.quotientAction_kernel] at hle

/-- Actual ambient conjugation on the core. -/
def Input.coreAmbientConjugation : J →* MulAut (commutatorCore L) := by
  let := h.component_normal
  exact MulAut.conjNormal

/-- The ambient action retains literal conjugation inside J. -/
@[simp] theorem Input.coreAmbientConjugation_apply (j : J) (d : commutatorCore L) :
    (h.coreAmbientConjugation j d : J) = j * (d : J) * j⁻¹ := by rfl

/-- Its kernel is exactly the centralizer of D. -/
theorem Input.coreAmbientConjugation_kernel :
    h.coreAmbientConjugation.ker = centralizer (commutatorCore L : Set J) := by
  ext j
  constructor
  · intro hj d hd
    have he := congrArg (fun a : MulAut (commutatorCore L) => (a ⟨d,hd⟩ : J)) hj
    change j * d * j⁻¹ = d at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hj
    apply MulEquiv.ext
    intro d
    apply Subtype.ext
    change j * (d : J) * j⁻¹ = d
    rw [← hj d d.property, mul_inv_cancel_right]

/-- Restriction to the actual action image preserves that exact kernel. -/
theorem Input.coreAmbientConjugation_rangeKernel :
    h.coreAmbientConjugation.rangeRestrict.ker =
      centralizer (commutatorCore L : Set J) := by
  rw [MonoidHom.ker_rangeRestrict, h.coreAmbientConjugation_kernel]

include h in
/-- The image of the ambient two-core centralizes the component image when D is abelian. -/
theorem Input.abelianCore_ambient_image_commutator
    (hc : IsMulCommutative (commutatorCore L)) :
    ⁅(pCore 2 J).map h.coreAmbientConjugation, L.map h.coreAmbientConjugation⁆ = ⊥ := by
  rw [← map_commutator]
  apply (Subgroup.map_eq_bot_iff _).mpr
  rw [h.coreAmbientConjugation_kernel]
  exact le_centralizer_iff_isMulCommutative.mpr hc

variable [IsElementaryAbelian 2 (commutatorCore L)]

/-- The faithful binary representation of the actual ambient action image. -/
noncomputable def Input.coreAmbientRepresentation :
    Representation (ZMod 2) h.coreAmbientConjugation.range (Additive (commutatorCore L)) := by
  let := h.component_normal
  exact Representation.NormalElementaryQuotient.representation (commutatorCore L)
    h.coreAmbientConjugation.rangeRestrict h.coreAmbientConjugation.rangeRestrict_surjective
    h.coreAmbientConjugation_rangeKernel

/-- Every image element acts by conjugation by its ambient representative. -/
theorem Input.coreAmbientRepresentation_apply (j : J) (v : Additive (commutatorCore L)) :
    ((h.coreAmbientRepresentation (h.coreAmbientConjugation.rangeRestrict j) v).toMul : J) =
      j * (v.toMul : J) * j⁻¹ := by
  let := h.component_normal
  exact Representation.NormalElementaryQuotient.representation_apply _ _ _ _ j v

/-- Passing to the action image removes precisely the conjugation kernel. -/
theorem Input.coreAmbientRepresentation_injective :
    Function.Injective h.coreAmbientRepresentation := by
  let := h.component_normal
  exact Representation.NormalElementaryQuotient.representation_injective _ _ _ _

/-- The image of L generates the entire module by its displacements. -/
theorem Input.coreAmbientRepresentation_full_commutator :
    Representation.BinaryOffender.subspaceCommutator h.coreAmbientRepresentation ⊤
      (L.map h.coreAmbientConjugation.rangeRestrict) = ⊤ := by
  let := h.component_normal
  let f := h.coreAmbientConjugation.rangeRestrict.comp L.subtype
  have hf : f.range = L.map h.coreAmbientConjugation.rangeRestrict := by
    rw [MonoidHom.range_comp, L.range_subtype]
  rw [← hf]
  apply Representation.BinaryOffender.commutator_eq_top_of_conjugation
    h.coreAmbientRepresentation (commutatorCore L) L
    (by rw [normalizer_eq_top]; exact le_top) f (MonoidHom.id _) Function.surjective_id
  · intro l d
    apply Additive.toMul.injective
    apply Subtype.ext
    exact h.coreAmbientRepresentation_apply l (Additive.ofMul d)
  · rw [commutator_comm]
    exact h.commutatorCore_idempotent

/-- Fixed vectors agree with the literal relative centralizer in D. -/
theorem Input.mem_coreAmbientFixedSpace (E : Subgroup J)
    (v : Additive (commutatorCore L)) :
    v ∈ Representation.BinaryOffender.fixedSpace h.coreAmbientRepresentation
      (E.map h.coreAmbientConjugation.rangeRestrict) ↔
        (v.toMul : J) ∈ centralizer (E : Set J) := by
  let := h.component_normal
  exact Representation.NormalElementaryQuotient.mem_fixedSpace_image _ _ _ _ E v

/-- A genuine maximum elementary subgroup gives an offender on the entire
elementary core, together with the cardinal bound on its actual fixed subgroup. -/
theorem Input.exists_coreAmbientOffender :
    ∃ E ∈ Stellmacher.elementaryAbelianMaxSubgroups R, ¬ E ≤ pCore 2 J ∧
      Representation.BinaryOffender.IsOffender h.coreAmbientRepresentation
        (E.map h.coreAmbientConjugation.rangeRestrict) ∧
      Nat.card (commutatorCore L) ≤
        Nat.card (E.map h.coreAmbientConjugation.rangeRestrict) *
        Nat.card (commutatorCore L ⊓ centralizer (E : Set J) : Subgroup J) := by
  let := h.component_normal
  obtain ⟨E, hE, hEN⟩ := h.exists_maxElementary_not_le_core
  have hDR : commutatorCore L ≤ R :=
    h.commutatorCore_le.trans (h.componentCore_eq_inf.le.trans
      (inf_le_left.trans h.radical.twoCore_le))
  refine ⟨E, hE, hEN, ?_, ?_⟩
  · apply Representation.NormalElementaryQuotient.maxElementary_isOffender
      (commutatorCore L) h.coreAmbientConjugation.rangeRestrict
      h.coreAmbientConjugation.rangeRestrict_surjective
      h.coreAmbientConjugation_rangeKernel R E hDR hE
    rw [h.coreAmbientConjugation_rangeKernel]
    exact fun hc => hEN (hc.trans h.core_centralizer_le)
  · simpa only [Nat.mul_comm] using Stellmacher.maxElementary_card_le_fixed_mul_image
      R (commutatorCore L) E hDR hE h.coreAmbientConjugation.rangeRestrict
      h.coreAmbientConjugation_rangeKernel

/-- An elementary whole core is an FF-module for its ambient action image.
The acting group here is J/C_J(D), not yet the specified SL₃(2). -/
theorem Input.coreAmbientRepresentation_isFFModule :
    Representation.BinaryOffender.IsFFModule h.coreAmbientRepresentation := by
  obtain ⟨E, _, _, hE, _⟩ := h.exists_coreAmbientOffender
  exact ⟨E.map h.coreAmbientConjugation.rangeRestrict, hE⟩

end CFSG.Quasithin.ChapterC.BinaryMS
