module

public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Coordinates
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.Basic
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# The fixed central root subgroup of a symplectic Sylow

The subgroup retains the actual inclusion of the Sylow center into Sp₄(F)
and the fixed subgroup of the specified automorphism. Fixed involutions can
be counted in this subgroup once their central placement is proved. This is
an interface for the two independent matrix calculations used in the
swapping case of Aschbacher--Smith E.1.14(1), printed p.214; it asserts
neither placement nor a fixed-point bound.
-/

@[expose] public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SwappingFixedRank
variable {F : Type*} [Field F]

/-- The literal intersection of the embedded Sylow center with the actor's
fixed subgroup. -/
def fixedCenter (S : Sylow 2 (Sp F)) (a : MulAut (Sp F)) : Subgroup (Sp F) :=
  ((center S).map (S : Subgroup (Sp F)).subtype) ⊓ a.fixedSubgroup

/-- Membership retains both the original center and the original action. -/
theorem mem_fixedCenter (S : Sylow 2 (Sp F)) (a : MulAut (Sp F)) (u : Sp F) :
    u ∈ fixedCenter S a ↔
      u ∈ (center S).map (S : Subgroup (Sp F)).subtype ∧ a u = u := by
  simp only [fixedCenter, mem_inf, MulAut.mem_fixedSubgroup]

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SwappingFixedRank
