module
public import Theory.GroupTheory.PCoreOddJoin
public import Theory.GroupTheory.SylowKernelCore

/-!
# Two-cores of normalized cubic joins

For a three-subgroup P normalized by a Sylow two-subgroup S, restrict to
P ∨ S and identify its embedded two-core with C_S(P). If S is
self-centralizing and P is nontrivial, this core is strictly smaller than S:
mutual normalization would make the coprime groups commute.

Source application: the collapsed-radical alternative in Aschbacher--Smith
10.2.5, printed p.748. The source application retains the actual quotient
map and is in BinaryThreeAction/OddSmallCoreInterval.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- The embedded two-core is exactly the Sylow centralizer of the normal cubic group. -/
theorem core_join_three_eq_sylow_centralizer (P : Subgroup G) (S : Sylow 2 G)
    (hp : IsPGroup 3 P) (hn : (S : Subgroup G) ≤ normalizer (P : Set G)) :
    (P ⊔ (S : Subgroup G)).pCoreIn 2 = (S : Subgroup G) ⊓ centralizer (P : Set G) := by
  let B := P ⊔ (S : Subgroup G)
  let A := P.subgroupOf B
  let R := S.subtype (show (S : Subgroup G) ≤ B from le_sup_right)
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le P.le_normalizer hn)
  have he := core_join_odd_eq_sylow_centralizer A hp.comap_subtype R
  have hm := congrArg (Subgroup.map B.subtype) he
  rw [map_pCoreIn_of_injective 2 _ B.subtype B.subtype_injective,
    Subgroup.map_sup,map_subgroupOf_eq_of_le (show P ≤ B from le_sup_left),
    show (R : Subgroup B).map B.subtype = (S : Subgroup G) from
      map_subgroupOf_eq_of_le le_sup_right] at hm
  refine hm.trans ?_
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    refine ⟨hy.1,?_⟩
    intro p hp
    exact congrArg Subtype.val (hy.2 (⟨p,mem_sup_left hp⟩ : B) hp)
  · intro hx
    refine ⟨⟨x,mem_sup_right hx.1⟩,⟨hx.1,?_⟩,rfl⟩
    intro p hp
    exact Subtype.ext (hx.2 p hp)

/-- A nontrivial normal cubic group cannot normalize a self-centralizing Sylow. -/
theorem three_not_normalizes_selfCentralizing_sylow
    (P : Subgroup G) (S : Sylow 2 G) (hp : IsPGroup 3 P) (hne : P ≠ ⊥)
    (hS : centralizer (S : Set G) = (S : Subgroup G))
    (hn : (S : Subgroup G) ≤ normalizer (P : Set G)) :
    ¬ P ≤ normalizer (S : Set G) := by
  intro hPS
  have hd := hp.disjoint_of_coprime S.isPGroup' (by decide : Nat.Coprime 3 2)
  have hcomm : ⁅P,(S : Subgroup G)⁆ = ⊥ := by
    apply bot_unique
    exact (le_inf (le_normalizer_iff_commutator_le_left.mp hn)
      (le_normalizer_iff_commutator_le_right.mp hPS)).trans hd.le_bot
  have hc := commutator_eq_bot_iff_le_centralizer.mp hcomm
  change P ≤ centralizer (S : Set G) at hc
  rw [hS] at hc
  exact hne (bot_unique ((le_inf le_rfl hc).trans hd.le_bot))

/-- With a self-centralizing Sylow, the normal cubic join has strictly smaller two-core. -/
theorem core_join_three_lt_selfCentralizing_sylow
    (P : Subgroup G) (S : Sylow 2 G) (hp : IsPGroup 3 P) (hne : P ≠ ⊥)
    (hS : centralizer (S : Set G) = (S : Subgroup G))
    (hn : (S : Subgroup G) ≤ normalizer (P : Set G)) :
    (P ⊔ (S : Subgroup G)).pCoreIn 2 < (S : Subgroup G) := by
  rw [core_join_three_eq_sylow_centralizer P S hp hn]
  apply lt_of_le_of_ne inf_le_left
  intro he
  have hc : (S : Subgroup G) ≤ centralizer (P : Set G) :=
    he.symm.le.trans inf_le_right
  exact three_not_normalizes_selfCentralizing_sylow P S hp hne hS hn
    ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _))

end Theory.GroupTheory
