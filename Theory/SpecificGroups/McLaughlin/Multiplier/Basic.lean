module

public import Theory.AtlasPort.OtherSporadic.McLaughlinModel
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# Covering interfaces for the McLaughlin triangle stabilizer

The base is the actual pointwise Leech 2-2-3 triangle stabilizer exported by
`Atlas.Sporadic.McLaughlin.Model`. Its proved perfectness and simplicity give
the quasisimplicity instance needed by the covering API. For a source group
identified modulo its center with this model, `sourceCover` retains the
literal quotient map and identifies its kernel with that center.

These are the model and map conventions for Aschbacher–Smith I.1.4(2),
printed p.408, and its A.2.19 application, printed pp.40–41. The multiplier
calculation is a separate obligation. In particular, no comparison with the
ATLAS degree-275 permutation-generated carrier is asserted here.
-/

namespace Theory.SpecificGroups.McLaughlin.Multiplier

open Atlas.Sporadic.McLaughlin Theory.GroupTheory PerfectCentralCovering

public instance model_isPerfect : Group.IsPerfect Model := perfect

public instance model_isQuasisimple : IsQuasisimple Model where
  simple := by
    let : IsSimpleGroup Model := isSimpleGroup
    have hz : Subgroup.center Model = ⊥ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
        (fun h => Group.IsPerfect.not_isMulCommutative Model
          (Subgroup.center_eq_top_iff.mp h))
    exact ((QuotientGroup.quotientMulEquivOfEq hz).trans
      QuotientGroup.quotientBot).isSimpleGroup

variable {E : Type*} [Group E] [Group.IsPerfect E]

/-- The source projection, followed by its specified model isomorphism. -/
@[expose] public def sourceCover (e : E ⧸ Subgroup.center E ≃* Model) :
    Cover E Model where
  toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center E))
  surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
  isPerfect := inferInstance
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

/-- The source-cover kernel is the original center, with no change of group. -/
public theorem sourceCover_kernel (e : E ⧸ Subgroup.center E ≃* Model) :
    (sourceCover e).toMonoidHom.ker = Subgroup.center E := by
  change (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center E))).ker = _
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

end Theory.SpecificGroups.McLaughlin.Multiplier
