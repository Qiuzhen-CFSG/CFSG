module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index

/-!
# A small commutator layer on a subgroup of index at most two

Let an involution normalize an elementary abelian two-group `U`. If a
subgroup `A ≤ U` has index at most two and `[A,t]` lies in an order-two
subgroup `Z`, then `[U,t]` has order at most four. If its order is four,
it contains `Z`. Neither invariance of `A` nor `Z ≤ U` is assumed.

The literal map `u ↦ [u,t]` is a homomorphism because `U` is abelian
and normalized by the actor. Its range is the full cyclic commutator.
Kernel inclusion and rank-nullity bound the full range by twice its
restriction to `A`. The restricted range lies in `Z`, so it has order
at most two; equality in the full bound forces it to equal `Z`.

This is the elementary counting step in Stellmacher (10.1), step (4),
printed p.60 of `refs/files/stellmacher-n-group.pdf`. The theorem is
independent of the local graph and classification hypotheses.
-/

namespace Subgroup
open scoped commutatorElement

/-- Restricting a homomorphism to a subgroup of index at most two reduces
its image cardinality by at most a factor of two. -/
public theorem range_card_le_twice_restriction
    {V G : Type*} [Group V] [Finite V] [Group G] [Finite G]
    (f : V →* G) (A : Subgroup V)
    (hindex : Nat.card V ≤ 2 * Nat.card A) :
    Nat.card f.range ≤ 2 * Nat.card (f.comp A.subtype).range := by
  let g := f.comp A.subtype
  let inclusion : g.ker → f.ker := fun x => ⟨x.val.val, x.property⟩
  have hinj : Function.Injective inclusion := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : f.ker => (z : V)) hxy
  have hker : Nat.card g.ker ≤ Nat.card f.ker :=
    Nat.card_le_card_of_injective inclusion hinj
  have hf : Nat.card V = Nat.card f.range * Nat.card f.ker := by
    rw [← index_ker, index_mul_card]
  have hg : Nat.card A = Nat.card g.range * Nat.card g.ker := by
    rw [← index_ker, index_mul_card]
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  have hbound : Nat.card f.range * Nat.card f.ker ≤
      2 * Nat.card g.range * Nat.card f.ker := by
    calc
      Nat.card f.range * Nat.card f.ker = Nat.card V := hf.symm
      _ ≤ 2 * Nat.card A := hindex
      _ = 2 * Nat.card g.range * Nat.card g.ker := by rw [hg]; ac_rfl
      _ ≤ 2 * Nat.card g.range * Nat.card f.ker := Nat.mul_le_mul_left _ hker
  exact Nat.le_of_mul_le_mul_right hbound hpos

public theorem commutator_card_le_four_of_index_two_small_layer
    {G : Type*} [Group G] [Finite G]
    (U A Z : Subgroup G) [IsElementaryAbelian 2 U]
    (actor : G) (hactor : actor ≠ 1 ∧ actor ^ 2 = 1)
    (hnormal : zpowers actor ≤ normalizer (U : Set G))
    (hAU : A ≤ U) (hindex : Nat.card U ≤ 2 * Nat.card A)
    (hcomm : ⁅A, zpowers actor⁆ ≤ Z) (hZcard : Nat.card Z = 2) :
    Nat.card (⁅U, zpowers actor⁆ : Subgroup G) ≤ 4 ∧
      (Nat.card (⁅U, zpowers actor⁆ : Subgroup G) = 4 →
        Z ≤ ⁅U, zpowers actor⁆) := by
  have hcommU : ⁅U, zpowers actor⁆ ≤ U :=
    le_normalizer_iff_commutator_le_left.mp hnormal
  have hUcentral : U ≤ centralizer (U : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  let f : U →* G := {
    toFun := fun point => ⁅(point : G), actor⁆
    map_one' := by simp
    map_mul' := by
      intro x y
      change ⁅(x : G) * (y : G), actor⁆ = ⁅(x : G), actor⁆ * ⁅(y : G), actor⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hy : ⁅(y : G), actor⁆ ∈ U :=
        hcommU (commutator_mem_commutator y.property (mem_zpowers actor))
      have hx : ⁅(x : G), actor⁆ ∈ U :=
        hcommU (commutator_mem_commutator x.property (mem_zpowers actor))
      have hxy : (x : G) * ⁅(y : G), actor⁆ = ⁅(y : G), actor⁆ * (x : G) :=
        (hUcentral x.property _ hy).symm
      have hcc : ⁅(y : G), actor⁆ * ⁅(x : G), actor⁆ =
          ⁅(x : G), actor⁆ * ⁅(y : G), actor⁆ :=
        (hUcentral hy _ hx).symm
      rw [hxy, mul_inv_cancel_right, hcc] }
  have hrange : f.range = ⁅U, zpowers actor⁆ := by
    apply le_antisymm
    · rintro point ⟨source, rfl⟩
      exact commutator_mem_commutator source.property (mem_zpowers actor)
    · apply commutator_le.mpr
      intro point hpoint mover hmover
      by_cases hmoverOne : mover = 1
      · simp [hmoverOne]
      have hcard : Nat.card (zpowers actor) = 2 := by
        rw [Nat.card_zpowers, orderOf_eq_prime hactor.2 hactor.1]
      obtain ⟨unique, _, huniq⟩ :=
        (Nat.card_eq_two_iff' (1 : zpowers actor)).mp hcard
      have hma : (⟨mover, hmover⟩ : zpowers actor) = ⟨actor, mem_zpowers actor⟩ :=
        (huniq _ (fun heq => hmoverOne (congrArg Subtype.val heq))).trans
          (huniq _ (fun heq => hactor.1 (congrArg Subtype.val heq))).symm
      have heq : mover = actor := congrArg Subtype.val hma
      exact ⟨⟨point, hpoint⟩, by change ⁅point, actor⁆ = ⁅point, mover⁆; rw [heq]⟩
  let A' := A.subgroupOf U
  let fA := f.comp A'.subtype
  have hAcard : Nat.card A' = Nat.card A :=
    Nat.card_congr (subgroupOfEquivOfLe hAU).toEquiv
  have hfA : fA.range ≤ Z := by
    rintro point ⟨source, rfl⟩
    exact hcomm (commutator_mem_commutator source.property (mem_zpowers actor))
  have hbound : Nat.card f.range ≤ 2 * Nat.card fA.range :=
    range_card_le_twice_restriction f A' (by rwa [hAcard])
  have hsmall : Nat.card fA.range ≤ 2 := (card_le_of_le hfA).trans_eq hZcard
  rw [hrange] at hbound
  refine ⟨by omega, ?_⟩
  intro hfour
  have hAeq : Nat.card fA.range = 2 := by omega
  have hAZ : fA.range = Z := eq_of_le_of_card_ge hfA (by rw [hAeq, hZcard])
  rw [← hAZ, ← hrange]
  rintro point ⟨source, rfl⟩
  exact ⟨source.val, rfl⟩

end Subgroup

