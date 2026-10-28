module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.Sections
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.Representation.CommutingFiveFixedRank

/-!
# The rank-six contradiction on the code section

On the literal P/U, restrict the action to the cyclic subgroup generated
by a fixed-point-free element of order five. An element centralizing that
generator preserves its own fixed space as a five-group module. Its rank
must therefore be divisible by four and cannot be six.

This proves the final linear contradiction in 8.2.8(6) without assuming
semisimplicity for the whole even-order dihedral group. The selection of
s=t or tv, its centralization, its fixed rank six, and the exclusion of
the cubic alternative are separate source obligations. This module does
not assert that T fails to normalize O²(I) before those are supplied.

Source: Aschbacher–Smith, Proposition 8.2.8(6), printed p.719 (PDF p.736).
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition
variable {G H : Type*} [Group G] [Group H] [Finite G]
  (I U : Subgroup G) [(U.subgroupOf (I.pCoreIn 2)).Normal]
  [IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))]

/-- The actual binary P/U cannot have a rank-six fixed space for an actor
commuting with its fixed-point-free order-five action. -/
theorem code_fixed_rank_obstruction
    (ρ : Representation (ZMod 2) H
      (Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))))
    (x s : H) (hx : orderOf x = 5) (hc : Commute s x)
    (hfree : ∀ p, ρ x p = p → p = 0)
    (hd : Module.finrank (ZMod 2) (LinearMap.ker (ρ s - LinearMap.id)) = 6) : False := by
  let X := zpowers x
  let σ : Representation (ZMod 2) X
      (Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))) := ρ.comp X.subtype
  have hp : IsPGroup 5 X := IsPGroup.of_card (p := 5) (n := 1) (by
    simpa only [X, Nat.card_zpowers, pow_one] using hx)
  have hf : σ.invariants = ⊥ := by
    apply bot_unique
    intro p hp
    exact hfree p (hp ⟨x, mem_zpowers x⟩)
  have hcomm (a : X) (p) : ρ s (σ a p) = σ a (ρ s p) := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp a.property
    have hsa : Commute s (a : H) := hn ▸ hc.zpow_right n
    change (ρ s * ρ (a : H)) p = (ρ (a : H) * ρ s) p
    rw [← map_mul, ← map_mul, hsa.eq]
  exact no_six_fixedRank_of_commuting_five σ hp hf (ρ s) hcomm hd

end CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition
