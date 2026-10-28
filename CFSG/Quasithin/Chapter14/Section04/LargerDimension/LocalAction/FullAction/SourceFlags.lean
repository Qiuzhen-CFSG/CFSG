module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.FullAction
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.SourceFlags

/-!
# Supplying the full action to the source flags

The action/component assembly supplies the `FullActionData` consumed by
`source_flags`. Its quotient is the one induced by the literal conjugation
map; the identity below verifies the exact marking used by that consumer.
Thus the full-action input of the flag argument is discharged once the outer
source owner supplies the earlier premises of `full_moved_space_action`.
The natural flags, middle quotient and marked parabolics remain with their
respective source producers.

Source: Aschbacher--Smith, 14.4.8(2), printed p.1009.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
variable {G : Type*} [Group G] [Finite G]

/-- Application to the precise full-action contract of `source_flags`.
The action and its quotient retain their literal formulas, without changing
the chosen moved group or the quotient coordinates. -/
noncomputable def FullMovedSpaceAction.toFullActionData
    {T : Sylow 2 G} {H E I₂ L₂ V₂ X : Subgroup G}
    (d : FullMovedSpaceAction T I₂ L₂ V₂ X) (hX : X ∈ YFamily H T V₂ E) :
    FullActionData H L₂ T V₂ E X hX where
  normalizes := d.normalizes
  action := conjugation _ _ d.normalizes
  action_eq_conjugation := rfl
  action_surjective := d.surjective
  action_kernel := d.kernel
  model := d.pslModel
  quotient := d.quotient
  quotient_map_eq := by
    ext a
    exact d.quotient_mk a

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction
