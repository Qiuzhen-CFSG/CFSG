module

public import Theory.GroupTheory.Amalgam.RankTwoTransport
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups

/-!
# The concrete binary linear flag amalgam

The point e₀ and plane v₂ = 0 give two flag stabilizers in SL₃(2).
The canonical projection to PSL₃(2) is injective; using that same projection
on all three subgroups gives an isomorphism of amalgams. The whole overlap
is the displayed Sylow two-subgroup and the parabolics generate PSL₃(2).

This constructs the model occurring at q = 2 in Aschbacher--Smith F.1.12(I)(1),
printed p. 262. It does not yet identify the two parabolics with S₄, prove the
general field case, or recognize an arbitrary amalgam.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.BinaryLinear

open Theory.GroupTheory
open Matrix.PSL3Two

/-- The two incident matrix stabilizers, with their whole intersection. -/
def matrixAmalgam : RankTwoAmalgam pointParabolicSL borelSL lineParabolicSL :=
  RankTwoAmalgam.ofSubgroups _ _ _ inf_le_left inf_le_right

theorem borel_le_point : borel ≤ pointParabolic :=
  pointParabolic_inf_line ▸ inf_le_left

theorem borel_le_line : borel ≤ lineParabolic :=
  pointParabolic_inf_line ▸ inf_le_right

/-- The amalgam inside the actual projective special linear group. -/
def amalgam : RankTwoAmalgam pointParabolic borel lineParabolic :=
  RankTwoAmalgam.ofSubgroups _ _ _ borel_le_point borel_le_line

/-- Both commuting squares use the actual quotient SL₃(2) → PSL₃(2). -/
noncomputable def projectIso : RankTwoAmalgam.Iso matrixAmalgam amalgam :=
  RankTwoAmalgam.ofSubgroupsMapIso project project_injective
    pointParabolicSL borelSL lineParabolicSL inf_le_left inf_le_right

theorem left_injective : Function.Injective amalgam.left :=
  RankTwoAmalgam.ofSubgroups_left_injective _ _ _ _ _

theorem right_injective : Function.Injective amalgam.right :=
  RankTwoAmalgam.ofSubgroups_right_injective _ _ _ _ _

/-- Here the whole overlap is Sylow; this equality is specific to q = 2. -/
theorem overlap_eq_sylow :
    pointParabolic ⊓ lineParabolic = (borelSylow : Subgroup PSL) :=
  pointParabolic_inf_line

/-- The two concrete parabolics generate the model group. -/
theorem parabolics_generate : pointParabolic ⊔ lineParabolic = ⊤ := by
  apply isCoatom_pointParabolic.2
  apply lt_of_le_of_ne le_sup_left
  intro h
  have hle : lineParabolic ≤ pointParabolic := h ▸ le_sup_right
  exact pointParabolic_ne_line
    (eq_of_le_of_not_lt hle (fun hlt =>
      isCoatom_pointParabolic.1 (isCoatom_lineParabolic.2 _ hlt))).symm

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.BinaryLinear
