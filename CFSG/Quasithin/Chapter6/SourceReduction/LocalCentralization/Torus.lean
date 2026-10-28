module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalDefs
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalSmallGenerationTorus
public import Theory.NumberTheory.BinaryTorusParity

/-!
# The cubic and the original rank-one torus

The actual Hall Cartan has order 2ⁿ−1. The witnessed cubic therefore forces
n even, independently of centralization or a module model. Once the source
torus argument proves n=2, this same cubic is the entire Cartan. Its placement
in the centralizing component then places the full rank-one Borel in the
omega centralizer. These are consequences of the literal source subgroups.

Source: Aschbacher--Smith, 5.1.13, printed pp.637--638.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

namespace LocalCartanWitness
variable {κ : GroupClass.{u}} {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
  (d : LocalCartanWitness T H A Y X D)
include d

/-- The local cubic already rules out odd field degree. -/
theorem even_exponent (h : Input κ T L W n)
    (c : CartanPair T L H A B) : Even n := by
  apply (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mp
  have hd := Subgroup.card_dvd_of_le (d.cubic_le.trans inf_le_left)
  rwa [d.cubic_card, c.left_card h.linear h.sylow_normalizes] at hd

/-- At degree two the actual escaping cubic exhausts the left Cartan. -/
theorem cartan_eq_cubic_of_exponent_eq_two
    (h : Input κ T L W n)
    (c : CartanPair T L H A B) (hn : n = 2) : A = D := by
  apply (eq_of_le_of_card_ge (d.cubic_le.trans inf_le_left) _).symm
  rw [d.cubic_card, c.left_card h.linear h.sylow_normalizes, hn]
  norm_num

/-- The final torus restriction supplies the entire Borel centralization
needed by the module argument, using the original Hall supplement. -/
theorem borel_centralizes_of_exponent_eq_two
    (h : Input κ T L W n)
    (c : CartanPair T L H A B) (hn : n = 2)
    (hXC : X ≤ omegaCentralizer T) : localBorel T L ≤ omegaCentralizer T := by
  rw [← c.left_sup_intersection h.sylow_normalizes]
  apply sup_le (inf_le_left.trans sylow_le_omegaCentralizer)
  rw [d.cartan_eq_cubic_of_exponent_eq_two h c hn]
  exact (d.cubic_le.trans inf_le_right).trans hXC

end LocalCartanWitness
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
