module

public import CFSG.Quasithin.ChapterG.Section08.Defs
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.Contracts

/-!
# The G.8/G.9 dihedral-product interface

The source G.8.6--G.8.8 argument constructs an actual injective homomorphism
from a finite product of odd-prime dihedral groups.  Section 08 records this
as `DihedralProduct`, while the G.9 contracts use the parallel name
`DihedralSystem`.  This module contains only the interface transport: it does
not assert Thompson's dihedral lemma or hide its complement hypotheses.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
G.8.6--G.8.8, printed pp.350--351.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section08

open Subgroup

universe u

variable {G : Type u} [Group G]

/-- Transport the actual product embedding used in G.8 to the G.9 contract.

The construction is field-preserving.  In particular, the homomorphism and
its injectivity proof are retained verbatim; this is not a family tag or a
collection of pairwise commuting subgroups.
-/
public def DihedralProduct.toDihedralSystem {n : ℕ}
    (D : DihedralProduct G n) :
    CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralSystem G n :=
  { prime := D.prime
    prime_isPrime := D.prime_isPrime
    prime_odd := D.prime_odd
    embedding := D.embedding
    injective := D.injective }

/-- The product range and the prime data are unchanged by the interface
transport.  This helper is useful when an extraction consumer is phrased in
terms of `DihedralSystem` but its witness was constructed in Section 08.
-/
public theorem DihedralProduct.toDihedralSystem_range {n : ℕ}
    (D : DihedralProduct G n) :
    (D.toDihedralSystem :
      CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralSystem G n).embedding.range =
      D.embedding.range := rfl

/-- Assemble the four G.9 extraction clauses from already constructed
Section-08 products.  The four product witnesses are explicit inputs: this
adapter does not discharge the G.8.6--G.8.8 mathematical obligations.
-/
public theorem dihedralExtraction_of_products
    {A X : Subgroup G} {n : ℕ}
    (h₀ : ∃ D : DihedralProduct G n,
      A ≤ D.embedding.range ∧ D.embedding.range ≤ X ⊔ A)
    (h₃ : ⁅CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.threeResidual X, A⁆ = ⊥ →
      ∃ D : DihedralProduct G n,
        A ≤ D.embedding.range ∧ D.embedding.range ≤ X ⊔ A ∧
          ∀ i, D.prime i = 3)
    (hLarge : ⁅CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.threeFiveResidual X, A⁆ ≠ ⊥ →
      ∃ D : DihedralProduct G n,
        A ≤ D.embedding.range ∧ D.embedding.range ≤ X ⊔ A ∧
          ∃ i, 5 < D.prime i)
    (h₅ : ⁅CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.threeFiveResidual X, A⁆ = ⊥ →
      ⁅CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.threeResidual X, A⁆ ≠ ⊥ →
      ∃ D : DihedralProduct G n,
        A ≤ D.embedding.range ∧ D.embedding.range ≤ X ⊔ A ∧
          ∃ i, D.prime i = 5) :
    CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralExtraction A X n := by
  refine {
    exists_system := ?_,
    cubic_system := ?_,
    large_prime_system := ?_,
    five_system := ?_ }
  · obtain ⟨D, hA, hX⟩ := h₀
    exact ⟨D.toDihedralSystem, hA, hX⟩
  · intro h
    obtain ⟨D, hA, hX, hp⟩ := h₃ h
    exact ⟨D.toDihedralSystem, hA, hX, hp⟩
  · intro h
    obtain ⟨D, hA, hX, hp⟩ := hLarge h
    exact ⟨D.toDihedralSystem, hA, hX, hp⟩
  · intro hcentral hnoncentral
    obtain ⟨D, hA, hX, hp⟩ := h₅ hcentral hnoncentral
    exact ⟨D.toDihedralSystem, hA, hX, hp⟩

end CFSG.Quasithin.ChapterG.Section08
