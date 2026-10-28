module

public import Theory.AlgebraicGroup.BNPair.WordSeparation

/-!
Uniqueness of Bruhat double-coset indices for an arbitrary Tits system.

The shortest-word separation theorem applies after comparing the two index
lengths, so membership in two Bruhat double cosets forces their quotient
indices to coincide.  The second theorem packages this result for explicit
factorizations through chosen normalizer representatives.  The argument uses
only the Tits-system generation, involution, exchange, and nontriviality axioms
encoded by `WordSeparation`.
-/

namespace Theory.AlgebraicGroup.TitsSystem

open scoped Pointwise

variable {X : Type*} [Group X]

/-- Two Bruhat double cosets of a Tits system sharing an element have the same index. -/
public theorem doubleCoset_index_unique (T : TitsSystem (X := X))
    {w v : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N} {x : X}
    (hw : x ∈ (T.B : Set X) * representativeSet T.B T.N w * (T.B : Set X))
    (hv : x ∈ (T.B : Set X) * representativeSet T.B T.N v * (T.B : Set X)) :
    w = v := by
  rcases le_total (T.wordLength w) (T.wordLength v) with h | h
  · exact T.eq_of_mem_doubleCosets_of_wordLength_le h hw hv
  · exact (T.eq_of_mem_doubleCosets_of_wordLength_le h hv hw).symm

/-- Equal factorizations through normalizer representatives have equal quotient indices. -/
public theorem index_eq_of_representative_factorizations (T : TitsSystem (X := X))
    {w v : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N}
    (nw nv : T.N)
    (hnw : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) nw = w)
    (hnv : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) nv = v)
    {b₁ b₂ c₁ c₂ : X}
    (hb₁ : b₁ ∈ T.B) (hb₂ : b₂ ∈ T.B)
    (hc₁ : c₁ ∈ T.B) (hc₂ : c₂ ∈ T.B)
    (hfactor : b₁ * (nw : X) * b₂ = c₁ * (nv : X) * c₂) :
    w = v := by
  apply T.doubleCoset_index_unique (x := b₁ * (nw : X) * b₂)
  · rw [B_mul_representativeSet_mul_B T.B T.N w nw hnw]
    exact ⟨b₁ * (nw : X), ⟨b₁, hb₁, (nw : X), Set.mem_singleton _, rfl⟩,
      b₂, hb₂, rfl⟩
  · rw [hfactor, B_mul_representativeSet_mul_B T.B T.N v nv hnv]
    exact ⟨c₁ * (nv : X), ⟨c₁, hc₁, (nv : X), Set.mem_singleton _, rfl⟩,
      c₂, hc₂, rfl⟩

end Theory.AlgebraicGroup.TitsSystem
