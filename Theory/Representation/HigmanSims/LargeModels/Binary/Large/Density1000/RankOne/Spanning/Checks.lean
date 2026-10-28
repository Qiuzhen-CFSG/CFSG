module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Blocks

/-!
# Index predicates for the Krylov inverse certificate

The inverse rows are checked against the shared `krylovTree` in bounded
finite batches.  `On` assembles those batches without re-evaluating a larger
universal computation, while `InverseCheck` records the exact left-inverse
orientation used by the final matrix identity.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne

def On (lo hi : ℕ) (P : ℕ → Prop) : Prop := ∀ i, lo ≤ i → i < hi → P i

theorem On.of_fin {P : ℕ → Prop} (lo count : ℕ)
    (h : ∀ i : Fin count, P (lo + i.val)) : On lo (lo + count) P := by
  intro i hlo hhi
  have hlt : i - lo < count := by omega
  simpa only [Nat.add_sub_of_le hlo] using h ⟨i - lo, hlt⟩

theorem On.append {P : ℕ → Prop} {lo mid hi : ℕ}
    (h₁ : On lo mid P) (h₂ : On mid hi P) : On lo hi P := by
  intro i hlo hhi
  by_cases hm : i < mid
  · exact h₁ i hlo hm
  · exact h₂ i (by omega) hhi

def InverseCheck (i : ℕ) : Prop :=
  krylovTree.product krylovInverseRows[i]! = 2 ^ i

instance (i : ℕ) : Decidable (InverseCheck i) :=
  inferInstanceAs (Decidable (_ = _))

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne
