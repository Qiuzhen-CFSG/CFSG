module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AutomorphismImage
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AutomorphismImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AutomorphismNoFF
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.ReducedFF

/-!
# The actual binary quotient of an MS group

The central omega module is a faithful FF-module for J/O₂(J). If the image
of conjugation on L/O₂(L) were the full automorphism group of SL₃(2), this
would contradict the proved binary automorphism FF exclusion. Thus its image
is exactly the inner group. Inverting the faithful inner embedding constructs
an actual isomorphism J/O₂(J) ≃ SL₃(2), compatible with the specified map on L.
The corresponding surjection and faithful central representation retain the
literal ambient conjugation formula.

The private `import all` is an intentional internal proof split: it supplies
the defining equation of `linearQuotientEquiv`, published below without
changing `AutomorphismImage` or exposing its definition bodies to clients.

These reductions discharge the graph-automorphism obstruction. They do not
classify the commutator core or identify its center with Ω₁Z(O₂(J)).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.32 proof,
printed pp.135–136; the remaining core rigidity is in C.1.34, pp.136–137.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS
open Subgroup BinaryLinear.OuterCyclic
open scoped IsMulCommutative
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R)
attribute [local instance] centralModule_elementary

private theorem linear_center : center (LinearGroup 3) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hz := (centerCongr (slEquivLinear 3).symm ⟨x, hx⟩).property
  have he : (slEquivLinear 3).symm x = 1 := (binary_center_eq_bot (by decide)).le hz
  exact (slEquivLinear 3).symm.map_eq_one_iff.mp he

include h

omit [Finite J] in
/-- The transported component quotient is the given matrix map followed by
the canonical matrix-to-linear-map equivalence. -/
theorem Input.linearQuotientEquiv_apply (x : L ⧸ pCore 2 L) :
    h.linearQuotientEquiv x = (slEquivLinear 3) (h.quotientEquiv x) := by
  rfl

/-- The genuine MS conditions exclude the full graph-automorphism image. -/
theorem Input.linearAction_range_eq_inner :
    h.linearAction.range = MulAut.innerSubgroup (LinearGroup 3) := by
  rcases h.linearAction_range_cases with hi | ht
  · exact hi
  · let e : (J ⧸ pCore 2 J) ≃* MulAut (LinearGroup 3) :=
      h.linearQuotientEquivRange.trans ((MulEquiv.subgroupCongr ht).trans topEquiv)
    let ρ := h.reducedRepresentation.comp e.symm.toMonoidHom
    have hf : Function.Injective ρ := h.reducedRepresentation_injective.comp e.symm.injective
    apply (AutomorphismNoFF.not_isFFModule_linear_of_faithful ρ hf).elim
    apply h.reducedRepresentation_isFFModule.map_equivariant h.reducedRepresentation ρ
      e.toMonoidHom e.injective (LinearEquiv.refl (ZMod 2) _)
    intro g v
    simp only [ρ, LinearEquiv.refl_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply]

/-- The core quotient is the concrete binary linear group, via actual conjugation. -/
noncomputable def Input.coreQuotientEquivLinear :
    (J ⧸ pCore 2 J) ≃* LinearGroup 3 :=
  h.linearQuotientEquivRange.trans
    ((MulEquiv.subgroupCongr h.linearAction_range_eq_inner).trans
      (MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot
        linear_center)).symm)

/-- The quotient identification recovers the original transported conjugation action. -/
theorem Input.coreQuotientEquivLinear_conj (j : J) :
    MulAut.conj (h.coreQuotientEquivLinear (QuotientGroup.mk' (pCore 2 J) j)) =
      h.linearAction j := by
  let e := MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot linear_center)
  have he := congrArg Subtype.val (e.apply_symm_apply
    (MulEquiv.subgroupCongr h.linearAction_range_eq_inner
      (h.linearQuotientEquivRange (QuotientGroup.mk' (pCore 2 J) j))))
  exact he.trans (h.linearQuotientEquivRange_mk j)

/-- The actual ambient two-core quotient, in the same matrix model as the input. -/
noncomputable def Input.coreQuotientEquiv :
    (J ⧸ pCore 2 J) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  h.coreQuotientEquivLinear.trans (slEquivLinear 3).symm

/-- The quotient projection with values in the actual special linear group. -/
noncomputable def Input.coreProjection :
    J →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  h.coreQuotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))

/-- The matrix projection factors through the specified actual quotient isomorphism. -/
theorem Input.coreQuotientEquiv_mk (j : J) :
    h.coreQuotientEquiv (QuotientGroup.mk' (pCore 2 J) j) = h.coreProjection j := by
  rfl

/-- Every matrix in SL₃(2) is induced by an ambient element. -/
theorem Input.coreProjection_surjective : Function.Surjective h.coreProjection :=
  h.coreQuotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The kernel is the intrinsic ambient two-core. -/
theorem Input.coreProjection_kernel : h.coreProjection.ker = pCore 2 J := by
  ext j
  change h.coreQuotientEquiv (QuotientGroup.mk' (pCore 2 J) j) = 1 ↔ _
  rw [h.coreQuotientEquiv.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff j

/-- On L, this projection is exactly the specified component-quotient map. -/
theorem Input.coreProjection_component (l : L) :
    h.coreProjection l = h.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) := by
  apply (slEquivLinear 3).injective
  change (slEquivLinear 3) ((slEquivLinear 3).symm
    (h.coreQuotientEquivLinear (QuotientGroup.mk' (pCore 2 J) l))) = _
  rw [MulEquiv.apply_symm_apply]
  apply MulAut.conj_injective_of_center_eq_bot linear_center
  rw [← h.linearQuotientEquiv_apply]
  exact (h.coreQuotientEquivLinear_conj l).trans (h.linearAction_component l)

/-- The ambient group is generated by its two-core and its given component. -/
theorem Input.core_sup_component : pCore 2 J ⊔ L = ⊤ := by
  have he := congrArg (fun S => S.comap h.linearAction) h.linearAction_component_image
  rw [← h.linearAction_range_eq_inner, MonoidHom.comap_range_self, comap_map_eq,
    h.linearAction_kernel, sup_comm] at he
  exact he

/-- The faithful central module, now acted on by the concrete matrix quotient. -/
noncomputable def Input.binaryRepresentation :
    Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      (Additive (centralModule J)) :=
  h.reducedRepresentation.comp h.coreQuotientEquiv.symm.toMonoidHom

/-- The transported matrix action is faithful. -/
theorem Input.binaryRepresentation_injective : Function.Injective h.binaryRepresentation :=
  h.reducedRepresentation_injective.comp h.coreQuotientEquiv.symm.injective

/-- The genuine maximum-elementary offender survives the quotient identification. -/
theorem Input.binaryRepresentation_isFFModule :
    Representation.BinaryOffender.IsFFModule h.binaryRepresentation := by
  apply h.reducedRepresentation_isFFModule.map_equivariant h.reducedRepresentation
    h.binaryRepresentation h.coreQuotientEquiv.toMonoidHom h.coreQuotientEquiv.injective
    (LinearEquiv.refl (ZMod 2) _)
  intro g v
  simp only [Input.binaryRepresentation, LinearEquiv.refl_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]

/-- Matrix images of ambient elements act by their literal ambient conjugation. -/
theorem Input.binaryRepresentation_apply (j : J) (v : Additive (centralModule J)) :
    ((h.binaryRepresentation (h.coreProjection j) v).toMul : J) =
      j * (v.toMul : J) * j⁻¹ := by
  change ((h.reducedRepresentation
    (h.coreQuotientEquiv.symm (h.coreQuotientEquiv (QuotientGroup.mk' (pCore 2 J) j)))
      v).toMul : J) = _
  rw [MulEquiv.symm_apply_apply]
  exact h.reducedRepresentation_apply j v

end CFSG.Quasithin.ChapterC.BinaryMS
