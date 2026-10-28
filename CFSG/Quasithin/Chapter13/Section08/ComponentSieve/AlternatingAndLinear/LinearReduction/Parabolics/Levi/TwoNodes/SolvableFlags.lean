module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.SolvableFlags
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.TwoNodes.ResidualImages

/-!
# The marked quotient of a solvable five-space flag with three-part nine

The intrinsic flag classification determines two distinct nonadjacent deleted
nodes from solvability and the three-part of the actual stabilizer order.
Specializing the constructed quotient to those nodes gives S₃ × S₃, with the
ambient O² residuals mapping onto the two ordered alternating factors. Every
quotient and marking premise is discharged by the geometric calculations.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
the rank-two parabolic step in 13.8.25, printed pp.959–960 (PDF pp.976–977).
This is the small Levi calculation used there; the full source-theorem
assembly remains with the surrounding parabolic argument.
-/

public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.SmallParabolicLevi.TwoNodes
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

/-- Solvability and three-part nine determine the two deleted, nonadjacent nodes. -/
theorem fiveFlag_cuts_eq_compl_pair_of_solvable_three_part (b : FiveBasis)
    (cuts : Set (Fin 4)) (hs : Group.IsSolvable (flagStabilizer b cuts))
    (h3 : (Nat.card (flagStabilizer b cuts)).factorization 3 = 2) :
    ∃ i j : Fin 4, i ≠ j ∧ (i.val + 1 < j.val ∨ j.val + 1 < i.val) ∧
      cuts = ({i, j} : Set (Fin 4))ᶜ :=
  cuts_eq_compl_pair_of_solvable_three_part b cuts hs h3

/-- The same classification in the deleted-node convention of `fiveParabolic`. -/
theorem fiveParabolic_nodes_eq_pair_of_solvable_three_part (b : FiveBasis)
    (nodes : Set (Fin 4)) (hs : Group.IsSolvable (fiveParabolic b nodes))
    (h3 : (Nat.card (fiveParabolic b nodes)).factorization 3 = 2) :
    ∃ i j : Fin 4, i ≠ j ∧ (i.val + 1 < j.val ∨ j.val + 1 < i.val) ∧
      nodes = ({i, j} : Set (Fin 4)) := by
  obtain ⟨i, j, hij, hn, hc⟩ :=
    fiveFlag_cuts_eq_compl_pair_of_solvable_three_part b nodesᶜ hs h3
  exact ⟨i, j, hij, hn, compl_injective hc⟩

/-- A solvable flag with three-part nine has the actual S₃ × S₃ quotient,
with the ambient node residuals identified with its ordered A₃ factors. -/
theorem fiveFlag_marked_quotient_of_solvable_three_part (b : FiveBasis)
    (cuts : Set (Fin 4)) (hs : Group.IsSolvable (flagStabilizer b cuts))
    (h3 : (Nat.card (flagStabilizer b cuts)).factorization 3 = 2) :
    ∃ i j : Fin 4, i ≠ j ∧ (i.val + 1 < j.val ∨ j.val + 1 < i.val) ∧
      cuts = ({i, j} : Set (Fin 4))ᶜ ∧
      ∃ e : (flagStabilizer b cuts ⧸ pCore 2 (flagStabilizer b cuts)) ≃*
          Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3),
        ((fiveNodeResidual b i).subgroupOf (flagStabilizer b cuts)).map
            (e.toMonoidHom.comp (QuotientGroup.mk' _)) =
          (alternatingGroup (Fin 3)).prod ⊥ ∧
        ((fiveNodeResidual b j).subgroupOf (flagStabilizer b cuts)).map
            (e.toMonoidHom.comp (QuotientGroup.mk' _)) =
          (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3)) := by
  obtain ⟨i, j, hij, hn, rfl⟩ :=
    fiveFlag_cuts_eq_compl_pair_of_solvable_three_part b cuts hs h3
  exact ⟨i, j, hij, hn, rfl, fiveTwoNodeQuotientEquiv b i j hn,
    fiveNodeResidual_map_twoNodeBlockAction_first b i j hn,
    fiveNodeResidual_map_twoNodeBlockAction_second b i j hn⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

end
