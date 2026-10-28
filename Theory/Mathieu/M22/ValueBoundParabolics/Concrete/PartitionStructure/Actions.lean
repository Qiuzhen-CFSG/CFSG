module

public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PartitionStructure.Restriction

/-!
# The genuine action on the three pairs

Two even double transpositions on the hexad lift the adjacent transpositions
of its three pairs. Six words exhaust the pair permutations. The genuine
surjective hexad restriction lifts these elements to M₂₂, and inclusion then
gives the same surjective pair action in the full design group.

These are the quotient actions used in Aschbacher–Smith E.4.3(2), printed
pp. 241–242; the intrinsic two-core identification is assembled separately.
-/

@[expose] public section
open scoped Pointwise
open Subgroup
namespace Sporadic.Mathieu.M22ValueBound.Concrete.PartitionStructure
def smallSwap₁ : smallGroup :=
  ⟨Equiv.swap (⟨1, by decide +kernel⟩ : m22Hexad123) (⟨3, by decide +kernel⟩ : m22Hexad123) *
    Equiv.swap (⟨2, by decide +kernel⟩ : m22Hexad123) (⟨10, by decide +kernel⟩ : m22Hexad123), by decide +kernel⟩

def smallSwap₂ : smallGroup :=
  ⟨Equiv.swap (⟨3, by decide +kernel⟩ : m22Hexad123) (⟨18, by decide +kernel⟩ : m22Hexad123) *
    Equiv.swap (⟨10, by decide +kernel⟩ : m22Hexad123) (⟨20, by decide +kernel⟩ : m22Hexad123), by decide +kernel⟩

def smallWords : Fin 6 → smallGroup :=
  ![1, smallSwap₁, smallSwap₂, smallSwap₁ * smallSwap₂,
    smallSwap₂ * smallSwap₁, smallSwap₁ * smallSwap₂ * smallSwap₁]

attribute [local instance] fintypePerm

theorem smallWords_exhaust :
    ∀ q : Equiv.Perm hexadPartition, ∃ i : Fin 6, smallAction (smallWords i) = q := by
  decide +kernel

theorem smallAction_surjective : Function.Surjective smallAction := by
  intro q
  obtain ⟨i, hi⟩ := smallWords_exhaust q
  exact ⟨smallWords i, hi⟩

noncomputable def toSmall : second →* smallGroup :=
  ((m22SetAction m22Hexad123).comp (Subgroup.inclusion second_le_hexad)).codRestrict
    smallGroup (by
      intro g
      change (⟨g.val, second_le_hexad g.property⟩ : MulAction.stabilizer M22 m22Hexad123) ∈
        smallGroup.comap (m22SetAction m22Hexad123)
      rw [second_preimage]
      exact g.property)

theorem toSmall_surjective : Function.Surjective toSmall := by
  intro p
  have hp : p.val ∈ (m22SetAction m22Hexad123).range := by
    rw [restriction_range]
    exact p.property.2
  obtain ⟨g, hg⟩ := hp
  have hg' : g ∈ second.subgroupOf (MulAction.stabilizer M22 m22Hexad123) := by
    rw [← second_preimage]
    change m22SetAction m22Hexad123 g ∈ smallGroup
    rw [hg]
    exact p.property
  exact ⟨⟨g.val, hg'⟩, Subtype.ext hg⟩

noncomputable def innerPairAction : second →* Equiv.Perm hexadPartition :=
  onFinset hexadPartition

noncomputable def outerPairAction : outerSecond →* Equiv.Perm hexadPartition :=
  onFinset hexadPartition

theorem innerPairAction_eq (g : second) :
    innerPairAction g = smallAction (toSmall g) := by
  ext s : 1
  apply Subtype.ext
  exact (restriction_agrees ⟨g.val, second_le_hexad g.property⟩
    (subset_hexad_of_mem s.property)).symm

theorem innerPairAction_surjective : Function.Surjective innerPairAction := by
  intro p
  obtain ⟨q, rfl⟩ := smallAction_surjective p
  obtain ⟨g, rfl⟩ := toSmall_surjective q
  exact ⟨g, innerPairAction_eq g⟩

theorem outerPairAction_surjective : Function.Surjective outerPairAction := by
  intro p
  obtain ⟨g, rfl⟩ := innerPairAction_surjective p
  exact ⟨⟨inclusion g.val, g.property⟩, rfl⟩

end Sporadic.Mathieu.M22ValueBound.Concrete.PartitionStructure
