module
public import Theory.Representation.BinaryOffender.RestrictionComparison
public import Theory.Representation.GeneratedSubgroupInvariants
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
/-!
# Generation by two fixed spaces at the codimension bound

If two actor subgroups generate an action containing L and the sum of
their fixed codimensions is at most the L-codimension, their fixed spaces
span the whole module. This is the sharp dimension step behind the
conjugate-span assertion in E.2.3(2).
-/
public section
namespace Representation.BinaryOffender
open Subgroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem fixedSpace_sup_eq_top_of_codim_sum
    (ρ : Representation (ZMod 2) G V) (A B L : Subgroup G)
    (hgen : L ≤ A ⊔ B) (hd : fixedCodim ρ A + fixedCodim ρ B ≤ fixedCodim ρ L) :
    fixedSpace ρ A ⊔ fixedSpace ρ B = ⊤ := by
  have he : fixedSpace ρ (A ⊔ B) = fixedSpace ρ A ⊓ fixedSpace ρ B :=
    ρ.invariants_comp_sup A B
  have hi : fixedSpace ρ A ⊓ fixedSpace ρ B ≤ fixedSpace ρ L := by
    rw [← he]
    exact fixedSpace_antitone ρ hgen
  have hi' := Submodule.finrank_mono hi
  have hs := (fixedSpace ρ A).finrank_sup_add_finrank_inf_eq (fixedSpace ρ B)
  have hA := fixedCodim_add_finrank ρ A
  have hB := fixedCodim_add_finrank ρ B
  have hL := fixedCodim_add_finrank ρ L
  have hle := Submodule.finrank_le (fixedSpace ρ A ⊔ fixedSpace ρ B)
  apply Submodule.eq_top_of_finrank_eq
  omega
end Representation.BinaryOffender
