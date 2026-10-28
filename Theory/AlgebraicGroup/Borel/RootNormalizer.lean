module

public import Theory.AlgebraicGroup.Borel.StandardPositiveSystemClassification.Defs
public import Theory.AlgebraicGroup.ClosedSubgroup.Normalizer

/-!
# Normalizers of the unipotent radical of a root Borel

The relative normality of the unipotent radical gives `B ≤ N(U)`. For the
reverse inclusion, a Borel--torus-normalizer--Borel factorization reduces an
element of `N(U)` to an element normalizing both `T` and `U`. Since `B = TU`,
that element normalizes `B`. Thus `N(U) ≤ N(B)`, and self-normalization of `B`
finishes the argument.

The two geometric inputs, Bruhat coverage and Borel self-normalization, remain
explicit. This module does not prove their existence. The radical and torus
factorization come from the actual `IsBorelOfPositiveSystem` witness, with
normality relative to `B`, not to the ambient group.

Sources: GLS3, Chapter 1, Theorems 1.6.3 and 1.11.3;
`refs/KGroup/GLS3/Chapter2St2.tex`, (6.2)--(6.3);
Borel, *Linear Algebraic Groups*, Theorem 11.16.
-/

namespace Theory.AlgebraicGroup

private theorem normalizer_le_of_factorization
    {G : Type*} [Group G] (B T U : Subgroup G)
    (hB : B = T ⊔ U) (hBU : B ≤ Subgroup.normalizer (U : Set G))
    (hcover : ∀ g : G, ∃ b n c : G,
      b ∈ B ∧ n ∈ Subgroup.normalizer (T : Set G) ∧ c ∈ B ∧ g = b * n * c) :
    Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (B : Set G) := by
  intro g hg
  obtain ⟨b, n, c, hb, hn, hc, rfl⟩ := hcover g
  have hnU : n ∈ Subgroup.normalizer (U : Set G) := by
    have h := (Subgroup.normalizer (U : Set G)).mul_mem
      ((Subgroup.normalizer (U : Set G)).mul_mem
        ((Subgroup.normalizer (U : Set G)).inv_mem (hBU hb)) hg)
      ((Subgroup.normalizer (U : Set G)).inv_mem (hBU hc))
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using h
  have hnB : n ∈ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hn hnU ⊢
    rw [hB, Subgroup.map_sup, hn, hnU]
  exact (Subgroup.normalizer (B : Set G)).mul_mem
    ((Subgroup.normalizer (B : Set G)).mul_mem
      (Subgroup.le_normalizer hb) hnB) (Subgroup.le_normalizer hc)

universe u
variable {k : Type u} [Field k] {K : Variety k} [AlgebraicGroup K]
  {T B : ClosedSubgroup K} {D : RootGroupData K T} {P : Set D.Root}

/-- A root Borel normalizes its root-generated unipotent radical. -/
public theorem IsBorelOfPositiveSystem.le_rootGenerated_normalizer
    (hB : IsBorelOfPositiveSystem D P B) :
    B.toSubgroup ≤ Subgroup.normalizer
      (RootSubgroupGenerated D P : Set (Variety.Point K)) := by
  rw [← hB.root_generated]
  exact Subgroup.le_normalizer_iff.mpr hB.radical.2.2.1

/-- Bruhat coverage reduces the radical normalizer to the Borel normalizer.
No self-normalization theorem is used in this reduction. -/
public theorem IsBorelOfPositiveSystem.rootGenerated_normalizer_le_of_bruhat
    (hB : IsBorelOfPositiveSystem D P B)
    (hcover : ∀ g : Variety.Point K, ∃ b n c : Variety.Point K,
      b ∈ B.toSubgroup ∧ n ∈ T.normalizer.toSubgroup ∧
        c ∈ B.toSubgroup ∧ g = b * n * c) :
    Subgroup.normalizer (RootSubgroupGenerated D P : Set (Variety.Point K)) ≤
      B.normalizer.toSubgroup := by
  apply normalizer_le_of_factorization B.toSubgroup T.toSubgroup
    (RootSubgroupGenerated D P)
  · rw [hB.torus_unipotent_generate, hB.root_generated]
  · exact hB.le_rootGenerated_normalizer
  · exact hcover

/-- Conditional root-radical normalizer equality. The geometric Bruhat and
Borel self-normalization premises must be proved before using this as the
unconditional source theorem. -/
public theorem IsBorelOfPositiveSystem.rootGenerated_normalizer_eq_of_bruhat
    (hB : IsBorelOfPositiveSystem D P B)
    (hcover : ∀ g : Variety.Point K, ∃ b n c : Variety.Point K,
      b ∈ B.toSubgroup ∧ n ∈ T.normalizer.toSubgroup ∧
        c ∈ B.toSubgroup ∧ g = b * n * c)
    (hself : B.normalizer = B) :
    Subgroup.normalizer (RootSubgroupGenerated D P : Set (Variety.Point K)) =
      B.toSubgroup := by
  apply le_antisymm
  · simpa only [hself] using hB.rootGenerated_normalizer_le_of_bruhat hcover
  · exact hB.le_rootGenerated_normalizer

end Theory.AlgebraicGroup
