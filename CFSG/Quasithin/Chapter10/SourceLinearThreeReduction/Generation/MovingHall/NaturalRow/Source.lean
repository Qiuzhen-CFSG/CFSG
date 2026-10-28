module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.ComponentModels

/-!
# Selecting and marking the original moving natural row

The original noncentral omega-center forces the local Thompson subgroup to
move the chosen module. The proved full-action B.5 classification supplies
literal natural coordinates on this same setup, or an actual SL₃(2)
component. Excluding the latter gives the original even-field quotient map.
The same full-action decomposition centralizes the crossed moved factor.

Thus `NaturalRowAt` needs no module-choice or point-control premise. The
moving-Hall assembly owner retains only the original Hall-placement proof.
Source: Aschbacher–Smith 10.1.1–2 and 10.2.2(1), pp.741–745.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 PointControl.Selection.ModuleChoice
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The actual moving-center source selects the original natural row and
both its literal quotient action and crossed-factor marking. -/
theorem source_natural_row : NaturalRowAt T := by
  intro L D H B ctx hthree
  have hJ := source_hstar_thompson_moves_of_omega_commutator D ctx.hstar ctx.moving
  obtain ⟨n,hn,e,mark⟩ :=
    (rankOneNatural_or_binaryThree_component D ctx.nonnormal ctx.not_a5 hJ).resolve_right hthree
  let : NeZero n := ⟨by omega⟩
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp ctx.nonnormal
  exact ⟨n,hn,GaloisField 2 n,inferInstance,inferInstance,inferInstance,
    GaloisField.card 2 n (by omega),e,mark,
    t,ht,htn,crossed_of_local_thompson D hJ ht htn⟩

end CFSG.Quasithin.Chapter10.MovingHall
