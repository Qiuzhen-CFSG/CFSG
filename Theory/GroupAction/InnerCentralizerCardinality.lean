module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.GroupAction.InnerInvolutionGeometry
public import Mathlib.GroupTheory.Sylow

/-!
# Orders of inner-automorphism centralizers

Intersecting an automorphism centralizer with the inner subgroup gives a
normal subgroup whose quotient embeds in the actual outer group. This gives
a divisibility bound, rather than just an inequality. Group isomorphisms
transport the full centralizer of the marked inner automorphism.

Separately, an element fixing a Sylow subgroup pointwise has a centralizer
containing the whole prime part of the group order. These are the elementary
order reductions used in Aschbacher--Smith 14.3.20, printed p.998.
-/

public section
open Subgroup
namespace MulAut
variable {G H : Type*} [Group G] [Group H]

/-- The quotient of the full centralizer by its inner part embeds in Out(G). -/
theorem centralizer_card_dvd_inner_mul_outer [Finite G] (a : MulAut G) :
    Nat.card (centralizer ({a} : Set (MulAut G))) ∣
      Nat.card (innerSubgroup G ⊓ centralizer ({a} : Set (MulAut G)) :
        Subgroup (MulAut G)) * Nat.card (Outer G) := by
  let C := centralizer ({a} : Set (MulAut G))
  let I := (innerSubgroup G).subgroupOf C
  have hc : Nat.card I = Nat.card (innerSubgroup G ⊓ C : Subgroup (MulAut G)) := by
    change Nat.card ((innerSubgroup G).subgroupOf C) = _
    rw [← inf_subgroupOf_right]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
  have hi : I.index ∣ (innerSubgroup G).index :=
    relIndex_dvd_index_of_normal (innerSubgroup G) C
  rw [← I.card_mul_index, hc]
  exact Nat.mul_dvd_mul_left _ hi

/-- In a centerless group, the inner centralizer is the original centralizer. -/
theorem card_inner_centralizer_conj (hz : center G = ⊥) (x : G) :
    Nat.card (innerSubgroup G ⊓ centralizer ({conj x} : Set (MulAut G)) :
      Subgroup (MulAut G)) = Nat.card (centralizer ({x} : Set G)) := by
  have hi := conj_injective_of_center_eq_bot hz
  let f : centralizer ({x} : Set G) →*
      (innerSubgroup G ⊓ centralizer ({conj x} : Set (MulAut G)) :
        Subgroup (MulAut G)) :=
    { toFun g := ⟨conj (g : G), ⟨⟨g, rfl⟩, mem_centralizer_singleton_iff.mpr (by
        rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp g.property])⟩⟩
      map_one' := Subtype.ext (map_one conj)
      map_mul' g h := Subtype.ext (map_mul conj g.val h.val) }
  have hf : Function.Bijective f := by
    constructor
    · intro g h he
      exact Subtype.ext (hi (congrArg Subtype.val he))
    · rintro ⟨a, ⟨⟨g, rfl⟩, hg⟩⟩
      have hc : g ∈ centralizer ({x} : Set G) := by
        apply mem_centralizer_singleton_iff.mpr
        apply hi
        simpa only [map_mul] using mem_centralizer_singleton_iff.mp hg
      exact ⟨⟨g, hc⟩, rfl⟩
  exact (Nat.card_congr (MulEquiv.ofBijective f hf).toEquiv).symm

/-- The centralizer order divides the element-centralizer order times |Out(G)|. -/
theorem centralizer_conj_card_dvd [Finite G] (hz : center G = ⊥) (x : G) :
    Nat.card (centralizer ({conj x} : Set (MulAut G))) ∣
      Nat.card (centralizer ({x} : Set G)) * Nat.card (Outer G) := by
  simpa only [card_inner_centralizer_conj hz] using
    centralizer_card_dvd_inner_mul_outer (conj x)

/-- Isomorphic groups have equally large centralizers of the same inner action. -/
theorem card_centralizer_conj_congr (e : G ≃* H) (x : G) :
    Nat.card (centralizer ({conj x} : Set (MulAut G))) =
      Nat.card (centralizer ({conj (e x)} : Set (MulAut H))) := by
  rw [← congr_conj e x]
  exact Nat.card_congr
    (Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv
      (MulAut.congr e) (conj x)).toEquiv

end MulAut

namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]

/-- Fixing a full Sylow subgroup retains every ambient p-power divisor. -/
theorem pow_dvd_card_centralizer_of_fixes_sylow (x : G)
    (S : Sylow p G) (hS : ∀ y : S, MulAut.conj x y = y)
    (hd : p ^ n ∣ Nat.card G) :
    p ^ n ∣ Nat.card (centralizer ({x} : Set G)) := by
  have hSC : (S : Subgroup G) ≤ centralizer ({x} : Set G) := by
    intro y hy
    exact mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp (hS ⟨y, hy⟩)).symm
  exact (S.pow_dvd_card_of_pow_dvd_card hd).trans (card_dvd_of_le hSC)

end Subgroup
