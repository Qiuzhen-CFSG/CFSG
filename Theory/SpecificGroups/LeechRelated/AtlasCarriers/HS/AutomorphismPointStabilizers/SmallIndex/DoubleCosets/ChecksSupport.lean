module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.DoubleCosets.Data

/-!
# Bounded row checks for the double-coset certificate

A row records its pivot image and a strict increase of its numerical key.
Twelve blocks of 480 rows cover a slice. This is only a decomposition of
finite checking; all decoded indices denote actual group-word products.
Source: the witness data and generator in this directory.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.SmallIndex.DoubleCosetCertificate

/-- A single row's image and its comparison with the following row. -/
def RowValid (k : Fin 3) (i : Fin 5760) : Prop :=
  rowMap k i 1 = pivot k ∧
    if h : i.val + 1 < 5760 then rowKey k i < rowKey k ⟨i.val + 1, h⟩ else True

instance (k : Fin 3) (i : Fin 5760) : Decidable (RowValid k i) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ (_ : Prop)))

def blockRow (b : Fin 12) (i : Fin 480) : Fin 5760 :=
  ⟨480 * b.val + i.val, by omega⟩

theorem allRows_of_blocks (k : Fin 3)
    (h : ∀ b i, RowValid k (blockRow b i)) : ∀ i, RowValid k i := by
  intro i
  have hh := h ⟨i.val / 480, by omega⟩ ⟨i.val % 480, Nat.mod_lt _ (by decide)⟩
  have he : blockRow ⟨i.val / 480, by omega⟩
      ⟨i.val % 480, Nat.mod_lt _ (by decide)⟩ = i := by
    apply Fin.ext
    simp only [blockRow]
    omega
  exact he ▸ hh

end Sporadic.LeechRelated.HS.SmallIndex.DoubleCosetCertificate
