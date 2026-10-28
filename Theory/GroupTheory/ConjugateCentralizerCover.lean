module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Index

/-!
# Conjugate centralizers with bounded index

If a group K normalizes E and A centralizes E₁, each K-conjugate of A
centralizes D ∩ E₁ᵏ for D ≤ E. Its index in D is bounded by the index of
E₁ in E. The proof combines conjugation invariance of index with the
subgroup intersection inequality; no ambient normality of E is needed.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, combined manuscript (1 March 2004), E.5.2, printed p.243.
-/

open Subgroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

public theorem conjugate_centralizer_cover (D E E₁ A K : Subgroup G)
    (hDE : D ≤ E)
    (hKE : K ≤ normalizer (E : Set G))
    (hAE₁ : A ≤ centralizer (E₁ : Set G)) (k : G) (hk : k ∈ K) :
    ∃ D₁ : Subgroup G, D₁ ≤ D ∧ D₁.relIndex D ≤ E₁.relIndex E ∧
      A.map (MulAut.conj k).toMonoidHom ≤ centralizer (D₁ : Set G) := by
  let f := (MulAut.conj k).toMonoidHom
  have hE : E.map f = E := mem_normalizer_iff_map_conj_eq.mp (hKE hk)
  refine ⟨D ⊓ E₁.map f, inf_le_left, ?_, ?_⟩
  · rw [inf_relIndex_left]
    calc
      (E₁.map f).relIndex D ≤ (E₁.map f).relIndex E :=
        relIndex_le_of_le_right hDE ((E₁.map f).subgroupOf E).index_ne_zero_of_finite
      _ = (E₁.map f).relIndex (E.map f) := by rw [hE]
      _ = E₁.relIndex E := relIndex_map_map_of_injective _ _ (MulAut.conj k).injective
  · have hAc : A.map f ≤ centralizer (E₁.map f : Set G) := by
      rintro _ ⟨a, ha, rfl⟩
      apply mem_centralizer_iff.mpr
      rintro _ ⟨e, he, rfl⟩
      simpa only [map_mul] using congrArg f (mem_centralizer_iff.mp (hAE₁ ha) e he)
    exact hAc.trans (centralizer_le inf_le_right)

end Subgroup
