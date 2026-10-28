module

public import Theory.Character.ModularBlock.Cartan

/-!
# Reindexing genuine principal Brauer families

Permuting the columns preserves completeness, linear independence and the
ordinary restriction equations. The Cartan matrix is permuted in both indices.
This is the change of ordered basic set used in Lyons (1972), p. 373, (3.1).
-/

public section
noncomputable section
open ModularBlock PrincipalBlockConstruction

namespace ModularBlock.Cartan
variable {G : Type*} [Group G] [Finite G]
variable {b : PrincipalCongruenceBlockData G} {n : ℕ}
/-- Relabel a complete genuine Brauer family by a permutation. -/
@[expose] def PrincipalBrauerFamily.reindex (a : PrincipalBrauerFamily b n) (e : Fin n ≃ Fin n) :
    PrincipalBrauerFamily b n where
  degree j := a.degree (e j)
  rep j := a.rep (e j)
  irreducible j := a.irreducible (e j)
  inBlock j := a.inBlock (e j)
  complete m ρ hi hb := by
    obtain ⟨j, hj⟩ := a.complete m ρ hi hb
    exact ⟨e.symm j, by rw [e.apply_symm_apply]; exact hj⟩
  independent := a.independent.comp e e.injective

/-- Relabel the genuine decomposition columns by the same permutation. -/
@[expose] def PrincipalDecompositionData.reindex (a : PrincipalDecompositionData b n)
    (e : Fin n ≃ Fin n) : PrincipalDecompositionData b n where
  family := a.family.reindex e
  decomposition i j := a.decomposition i (e j)
  restriction i hi g hg := by
    rw [a.restriction i hi g hg]
    exact (e.sum_comp (fun j => (a.decomposition i j : ℂ) *
      BrauerCharacter.value b (a.family.rep j) g)).symm

/-- The relabeling permutes both Cartan indices. -/
@[simp] theorem PrincipalDecompositionData.reindex_cartan
    (a : PrincipalDecompositionData b n) (e : Fin n ≃ Fin n) (i j : Fin n) :
    (a.reindex e).cartan i j = a.cartan (e i) (e j) := rfl
end ModularBlock.Cartan

