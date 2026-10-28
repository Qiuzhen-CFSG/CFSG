module

public import Theory.AlgebraicGroup.BNPair.StandardParabolicCore
public import Mathlib.Order.Atoms

/-!
# Maximal standard parabolics

Deleting one distinguished generator from a Tits system gives a maximal proper
subgroup. The standard-parabolic classification identifies any overgroup with
another subset of the distinguished generators; such a subset either omits the
same generator or is the full set.

This is the maximality consequence of GLS3, Theorem 2.6.5(b) and Definition
2.6.6, `refs/KGroup/GLS3/chapter2.tex`. The argument uses only the abstract
Tits-system axioms, not simplicity of the ambient group.
-/

namespace Theory.AlgebraicGroup.TitsSystem

variable {G : Type*} [Group G]

/-- Omitting one distinguished generator gives a maximal proper parabolic. -/
public theorem standardParabolic_isCoatom (T : TitsSystem (X := G))
    {s : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N} (hs : s ∈ T.S) :
    IsCoatom (T.standardParabolic (T.S \ {s})) := by
  have hI : T.S \ {s} ⊆ T.S := Set.sdiff_subset
  apply isCoatom_iff_ge_of_le.mpr
  constructor
  · intro htop
    have heq : T.S \ {s} = T.S :=
      (T.standardParabolic_eq_iff hI (Set.Subset.refl _)).mp
        (htop.trans T.standardParabolic_S.symm)
    have : s ∈ T.S \ {s} := heq.symm ▸ hs
    exact this.2 (Set.mem_singleton s)
  · intro H hH hPH
    have hBH : T.B ≤ H := (T.B_le_standardParabolic _).trans hPH
    have hclass := T.subgroup_eq_standardParabolic_simpleIndices H hBH
    have hIH : T.S \ {s} ⊆ T.simpleIndices H :=
      (T.standardParabolic_le_iff hI (T.simpleIndices_subset H)).mp
        (by rwa [← hclass])
    have hsH : s ∉ T.simpleIndices H := by
      intro hmem
      have heq : T.simpleIndices H = T.S := by
        apply Set.Subset.antisymm (T.simpleIndices_subset H)
        intro t ht
        by_cases hts : t = s
        · simpa only [hts] using hmem
        · exact hIH ⟨ht, hts⟩
      exact hH (hclass.trans (by rw [heq, T.standardParabolic_S]))
    rw [hclass]
    apply T.standardParabolic_mono
    intro t ht
    exact ⟨T.simpleIndices_subset H ht, fun hts => hsH (hts ▸ ht)⟩

end Theory.AlgebraicGroup.TitsSystem
