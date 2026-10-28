module
public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# Coordinate images preserve subgroup generation

The coordinate homomorphism sends a join of literal subgroups of the
section domain to the join of their binary subspaces. The proof transports
the join into the domain and then through the subgroup/subspace order
isomorphism. The tensor-plane application retains every original conjugate.
-/

@[expose] public section
namespace Representation.BinaryConjugationSection
open Subgroup
variable {G : Type*} [Group G] {H S E : Subgroup G}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} (d : BinaryConjugationSection H S E ρ)

theorem imageSpace_iSup {ι : Sort*} (B : ι → Subgroup G) (hB : ∀ i, B i ≤ S) :
    d.imageSpace (⨆ i, B i) = ⨆ i, d.imageSpace (B i) := by
  have he : (⨆ i, B i).subgroupOf S = ⨆ i, (B i).subgroupOf S := by
    apply Subgroup.map_subtype_inj.mp
    rw [map_subgroupOf_eq_of_le (iSup_le hB),Subgroup.map_iSup]
    exact iSup_congr fun i => (map_subgroupOf_eq_of_le (hB i)).symm
  let f : Subgroup (Multiplicative W) ≃o Submodule (ZMod 2) W :=
    Subgroup.toAddSubgroup'.trans (AddSubgroup.toZModSubmodule 2)
  change f (((⨆ i, B i).subgroupOf S).map d.coordinates) =
    ⨆ i, f (((B i).subgroupOf S).map d.coordinates)
  rw [he,Subgroup.map_iSup,f.map_iSup]

end Representation.BinaryConjugationSection
