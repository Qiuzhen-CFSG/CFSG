module
public import Theory.SpecificGroups.Rudvalis.Model.ExtraspecialFive.X
public import Theory.SpecificGroups.Rudvalis.Model.ExtraspecialFive.Y
public import Theory.SpecificGroups.Rudvalis.Model.ExtraspecialFive.R

/-!
# A nonabelian five-local configuration in the actual Rudvalis carrier

The checked words x,y have fifth power one and a nontrivial central commutator.
The checked word r inverts both x and y and fixes their commutator. Every
identity is checked on all 4060 letters; noncommutation is witnessed on letter
zero. No normalizer shape, order, or simplicity claim is used in these checks.

Source: GLS III, Table 5.3r, printed p.279, motivates this configuration in
5^(1+2).Q8.4. The actual witnesses come from the attributed ATLAS generators;
see `source/README.md`.
-/

open scoped commutatorElement
namespace Rudvalis.ExtraspecialFive
set_option maxRecDepth 30000
set_option Elab.async false

public theorem x_fifth : x ^ 5 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply Data.allFin
  decide +kernel

public theorem y_fifth : y ^ 5 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply Data.allFin
  decide +kernel

public theorem commutator_fifth : ⁅x, y⁆ ^ 5 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply Data.allFin
  decide +kernel

public theorem x_commute_commutator : Commute x ⁅x, y⁆ := by
  apply Subtype.ext
  apply Equiv.ext
  apply Data.allFin
  decide +kernel

public theorem y_commute_commutator : Commute y ⁅x, y⁆ := by
  apply Subtype.ext
  apply Equiv.ext
  apply Data.allFin
  decide +kernel

public theorem xy_ne_yx : x * y ≠ y * x := by
  intro h
  have he := congrArg (fun g : Model => (modelSubgroup.subtype g) 0) h
  have hn : (modelSubgroup.subtype (x * y)) 0 ≠ (modelSubgroup.subtype (y * x)) 0 := by
    decide +kernel
  exact hn he

public theorem commutator_ne_one : ⁅x, y⁆ ≠ 1 := by
  intro h
  exact xy_ne_yx (commutatorElement_eq_one_iff_mul_comm.mp h)

public theorem r_inverts_x : r * x * r⁻¹ = x⁻¹ := by
  apply Subtype.ext
  apply Equiv.ext
  apply Data.allFin
  decide +kernel

public theorem r_inverts_y : r * y * r⁻¹ = y⁻¹ := by
  apply Subtype.ext
  apply Equiv.ext
  apply Data.allFin
  decide +kernel

public theorem r_commute_commutator : Commute r ⁅x, y⁆ := by
  apply Subtype.ext
  apply Equiv.ext
  apply Data.allFin
  decide +kernel

end Rudvalis.ExtraspecialFive
