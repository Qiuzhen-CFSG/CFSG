module
public import Theory.GroupTheory.ConjugateCosetBlocks
public import Theory.GroupTheory.ConjugateCosetOrbit
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.Index

/-!
# Stabilizer and number of conjugates of a normalized coset

Let `M` be finite, normalized by `C(j)`, and disjoint from `C(j)`. The
setwise conjugation stabilizer of `jM` is exactly `M C(j)`, expressed as
the join transported to `ConjAct G`. Consequently the number of conjugate
cosets is the index of that join. This gives the subgroup-index calculation
in Brauer, *On finite Desarguesian planes I*, equation (2.7) and (2E), p. 120.
No involution assumption or finiteness of the ambient group is needed.

The coset is the conjugation orbit of `j` under `M` and is a block. If `g`
fixes the coset, then `g • j = m • j` for some `m ∈ M`, so `m⁻¹g` stabilizes
`j`. Conversely the block property shows that `M` and the stabilizer of `j`
fix the coset. The orbit-stabilizer index formula then yields the count.
The private action lemma isolates this argument without conjugation notation.
-/

open scoped Pointwise
namespace Theory.GroupTheory
private theorem stabilizer_eq_sup_of_orbit_eq_block
    {K X : Type*} [Group K] [MulAction K X] (H : Subgroup K) (a : X) (B : Set X)
    (hB : MulAction.IsBlock K B) (ho : MulAction.orbit H a = B) :
    MulAction.stabilizer K B = H ⊔ MulAction.stabilizer K a := by
  have ha : a ∈ B := ho ▸ MulAction.mem_orbit_self a
  apply le_antisymm
  · intro g hg
    have hga : g • a ∈ B := by
      rw [← MulAction.mem_stabilizer_iff.mp hg]
      exact Set.smul_mem_smul_set ha
    rw [← ho] at hga
    obtain ⟨m, hm⟩ := hga
    have hc : (m : K)⁻¹ * g ∈ MulAction.stabilizer K a := by
      change ((m : K)⁻¹ * g) • a = a
      rw [mul_smul, ← hm]
      exact inv_smul_smul (m : K) a
    have hgprod : g = (m : K) * ((m : K)⁻¹ * g) := by group
    rw [hgprod]
    exact (H ⊔ MulAction.stabilizer K a).mul_mem ((show H ≤ H ⊔ MulAction.stabilizer K a from le_sup_left) m.property)
      ((show MulAction.stabilizer K a ≤ H ⊔ MulAction.stabilizer K a from le_sup_right) hc)
  · apply sup_le
    · intro g hg
      apply hB.smul_eq_of_mem ha
      rw [← ho]
      exact ⟨⟨g, hg⟩, rfl⟩
    · exact hB.stabilizer_le ha

/-- The setwise conjugation stabilizer of the coset is the expected subgroup join. -/
public theorem stabilizer_conjugate_coset_eq {G : Type*} [Group G] (M : Subgroup G) [Finite M] (j : G)
    (hn : Subgroup.centralizer ({j} : Set G) ≤ Subgroup.normalizer (M : Set G))
    (hd : Disjoint M (Subgroup.centralizer ({j} : Set G)))
    :
    MulAction.stabilizer (ConjAct G) (j • (M : Set G)) =
      ((M ⊔ Subgroup.centralizer ({j} : Set G)).map ConjAct.toConjAct.toMonoidHom :
        Subgroup (ConjAct G)) := by
  rw [Subgroup.map_sup]
  have hc : ((Subgroup.centralizer ({j} : Set G)).map ConjAct.toConjAct.toMonoidHom :
      Subgroup (ConjAct G)) =
      MulAction.stabilizer (ConjAct G) j := by
    rw [Subgroup.centralizer_eq_comap_stabilizer]
    exact Subgroup.map_comap_eq_self_of_surjective ConjAct.toConjAct.surjective _
  rw [hc]
  exact stabilizer_eq_sup_of_orbit_eq_block _ _ _
    (isBlock_conjugate_coset_of_centralizer_normalizes M j hn hd)
    (orbit_conjugate_eq_coset M j hn hd)

/-- The family of conjugate cosets is counted by the corresponding subgroup index. -/
public theorem ncard_conjugate_coset_orbit_eq_index {G : Type*} [Group G] (M : Subgroup G) [Finite M] (j : G)
    (hn : Subgroup.centralizer ({j} : Set G) ≤ Subgroup.normalizer (M : Set G))
    (hd : Disjoint M (Subgroup.centralizer ({j} : Set G)))
    :
    (MulAction.orbit (ConjAct G) (j • (M : Set G))).ncard =
      (M ⊔ Subgroup.centralizer ({j} : Set G)).index := by
  rw [← MulAction.index_stabilizer, stabilizer_conjugate_coset_eq M j hn hd]
  exact Subgroup.index_map_equiv _ ConjAct.toConjAct
end Theory.GroupTheory

