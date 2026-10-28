module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.Classification

/-!+# Source constraints on the terminal offender representation

The group identity `[V₀,Ñ] = V₀`, where Ñ is the inverse image of the
offender group, implies that the linear commutators span V₀. In particular
there is no nonzero trivial quotient. This does not assert that the fixed
space vanishes: nonsplit extensions by a central submodule remain possible.

The actual subgroup O₂(Ẏ_F) lies in N. Restricting to N preserves its fixed
space, which contains the marked four-dimensional V. An intertwining
identification carries this bound to the image of that same subgroup in
the model. It must not be replaced by an unmarked abstract two-subgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, final
proof of 15.3.1, printed p.1155 (combined manuscript, 1 March 2004).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.SourceInput

open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- Group commutator generation is generation by actual linear displacements
for the restricted offender action. -/
theorem offenderAction_moved_eq_top : moved d.offenderAction ⊤ = ⊤ := by
  let C : Subgroup (moduleClosure V) :=
    (moved d.offenderAction ⊤).toAddSubgroup.toSubgroup'
  have hVC : moduleClosure V ≤ C.map (moduleClosure V).subtype := by
    conv_lhs => rw [d.closure_commutator_offenderCover, commutator_comm]
    apply commutator_le.mpr
    intro g hg v hv
    let w : Additive (moduleClosure V) := Additive.ofMul ⟨v, hv⟩
    let a : d.offenderGroup := ⟨coreProjection g, hg⟩
    refine ⟨(d.offenderAction a w - w).toMul, ?_, ?_⟩
    · change d.offenderAction a w - w ∈ moved d.offenderAction ⊤
      exact Submodule.subset_span ⟨a, mem_top a, w, Submodule.mem_top, rfl⟩
    · change ((quotientAction V d.centralizer_isTwoGroup d.core_centralizes
        (coreProjection g) w).toMul : H) / v = ⁅g, v⁆
      rw [quotientAction_apply, div_eq_mul_inv]
      rfl
  apply top_unique
  intro w _
  obtain ⟨v, hv, he⟩ := hVC w.toMul.property
  have heq : v = w.toMul := Subtype.ext he
  subst v
  exact hv

/-- Every linear map to a trivial offender module is zero. Thus fixed
direct summands can be removed without discarding nonsplit central kernels. -/
theorem linearMap_eq_zero_of_trivial_action {W : Type*}
    [AddCommGroup W] [Module (ZMod 2) W]
    (f : Additive (moduleClosure V) →ₗ[ZMod 2] W)
    (hf : ∀ g v, f (d.offenderAction g v) = f v) : f = 0 := by
  have hm : moved d.offenderAction ⊤ ≤ f.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, _, v, _, rfl⟩
    change f (d.offenderAction a v - v) = 0
    rw [map_sub, hf, sub_self]
  rw [d.offenderAction_moved_eq_top] at hm
  apply LinearMap.ext
  intro v
  exact hm Submodule.mem_top

include d in
/-- The dimension of the original marked subgroup bounds the whole module. -/
theorem module_finrank_ge_four :
    4 ≤ Module.finrank (ZMod 2) (Additive (moduleClosure V)) := by
  calc
    4 = Module.finrank (ZMod 2) (planeSubspace V V) := d.vector_finrank.symm
    _ ≤ _ := (planeSubspace V V).finrank_le

/-- O₂(Ẏ_F), viewed inside the offender group through its actual inclusion. -/
noncomputable abbrev firstCoreInOffender : Subgroup d.offenderGroup :=
  ((d.YF.map coreProjection).pCoreIn 2).subgroupOf d.offenderGroup

/-- Restriction to N loses no elements of this particular local core. -/
theorem firstCoreInOffender_map :
    d.firstCoreInOffender.map d.offenderGroup.subtype =
      (d.YF.map coreProjection).pCoreIn 2 :=
  map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans d.first_image_le)

/-- The four-dimensional source subspace is fixed by the restricted local core. -/
theorem vector_fixed_offender :
    planeSubspace V V ≤ fixedSpace d.offenderAction d.firstCoreInOffender := by
  change planeSubspace V V ≤ fixedSpace
    ((quotientAction V d.centralizer_isTwoGroup d.core_centralizes).comp
      d.offenderGroup.subtype) d.firstCoreInOffender
  rw [fixedSpace_comp_map, d.firstCoreInOffender_map]
  exact d.vector_fixed

/-- The actual local core has at least four independent fixed vectors. -/
theorem firstCore_fixed_finrank_ge_four :
    4 ≤ Module.finrank (ZMod 2) (fixedSpace d.offenderAction d.firstCoreInOffender) := by
  calc
    4 = Module.finrank (ZMod 2) (planeSubspace V V) := d.vector_finrank.symm
    _ ≤ _ := Submodule.finrank_mono d.vector_fixed_offender

/-- An action equivalence preserves the bound on the *marked* core image.
No classification or small fixed-space calculation is assumed. -/
theorem model_firstCore_fixed_finrank_ge_four
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) E W) (e : ActionEquiv d.offenderAction σ) :
    4 ≤ Module.finrank (ZMod 2)
      (fixedSpace σ (d.firstCoreInOffender.map e.groupEquiv.toMonoidHom)) := by
  rw [← fixedSpace_map_equivariant d.offenderAction σ e.groupEquiv.toMonoidHom
    e.linearEquiv e.intertwines, e.linearEquiv.finrank_map_eq]
  exact d.firstCore_fixed_finrank_ge_four

/-- A computed bound below four on the correctly marked model is incompatible
with the source configuration. Central quotients require their own transport. -/
theorem not_model_firstCore_fixed_finrank_lt_four
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) E W) (e : ActionEquiv d.offenderAction σ) :
    ¬ Module.finrank (ZMod 2)
      (fixedSpace σ (d.firstCoreInOffender.map e.groupEquiv.toMonoidHom)) < 4 :=
  Nat.not_lt_of_ge (d.model_firstCore_fixed_finrank_ge_four σ e)

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.SourceInput
