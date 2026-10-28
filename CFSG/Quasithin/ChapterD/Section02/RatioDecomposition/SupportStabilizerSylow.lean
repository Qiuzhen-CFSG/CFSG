module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.OrbitSupports
public import Theory.Representation.BinaryOffender.IrreducibleOrbitAction
public import Theory.GroupTheory.SylowNormalRestriction
public import Mathlib.Data.Finite.Perm
/-!
# Sylow restriction to a support stabilizer

With at most two literal factors, their ambient permutation group is abelian.
A support stabilizer is therefore normal, so the supplied ambient Sylow
subgroup restricts to a Sylow subgroup of that actual stabilizer.

Source: Aschbacher--Smith 15.1.2, printed p.1085.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G} {U : Submodule (ZMod 2) V}
  (c : FactorData ρ K U) (d : Decomposition c.representation)
namespace FactorData
theorem ambient_space_stabilizer_normal_of_count
    (π : G →* Equiv.Perm d.Index)
    (hs : ∀ g i, (c.ambientFactor d i).space.map (ρ g) =
      (c.ambientFactor d (π g i)).space)
    (hc : Nat.card d.Index ≤ 2) (i : d.Index) :
    (subspaceStabilizer ρ (c.ambientFactor d i).space).Normal := by
  let : IsMulCommutative (Equiv.Perm d.Index) :=
    Equiv.Perm.isMulCommutative_iff_card_le_two.mpr hc
  have hinj := (c.ambient_spaces_independent d).injective (c.ambient_space_ne_bot d)
  constructor
  intro x hx g
  have hxi : π x i = i := hinj ((hs x i).symm.trans
    ((subspace_map_eq_iff ρ _ x).mpr hx))
  apply (subspace_map_eq_iff ρ _ _).mp
  rw [hs,map_mul,map_mul,map_inv]
  have he : π g * π x * (π g)⁻¹ = π x := by
    rw [mul_comm (π g) (π x),mul_assoc,mul_inv_cancel,mul_one]
  rw [he,hxi]

variable [Finite G]
theorem exists_support_stabilizer_sylow_of_count
    (π : G →* Equiv.Perm d.Index)
    (hs : ∀ g i, (c.ambientFactor d i).space.map (ρ g) =
      (c.ambientFactor d (π g i)).space)
    (hc : Nat.card d.Index ≤ 2) (P : Sylow 2 G) (i : d.Index) :
    ∃ S : Sylow 2 (subspaceStabilizer ρ (c.ambientFactor d i).space),
      (S : Subgroup (subspaceStabilizer ρ (c.ambientFactor d i).space)).map
        (subspaceStabilizer ρ (c.ambientFactor d i).space).subtype =
      (P : Subgroup G) ⊓ subspaceStabilizer ρ (c.ambientFactor d i).space := by
  let := c.ambient_space_stabilizer_normal_of_count d π hs hc i
  exact P.exists_sylow_map_eq_inf_of_normal _
end FactorData
end CFSG.Quasithin.ChapterD.RatioDecomposition
