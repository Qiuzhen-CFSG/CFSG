module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.RotationTest

/-!
# Indexed certificates for rotated Sylow representatives

An indexed copy of the original rows gives membership without scanning the
whole list for every product. The checker still tests factor membership and
uses the original three-point equality test. Its soundness theorem applies
`rotationTest_sound`, with precisely the original factors and rows.
Source: Parrott (1972), §5, p.683; CommonFactorCover/source/README.md.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.Rotations

/-- A row stores its word in 19 bits and its original support above those bits. -/
def packedRow (data i : Nat) : Row :=
  let n := (data >>> (64 * i)) % (2^64)
  (n % (2^19), n / (2^19))

/-- A witness stores a normal-form index and an original-row position. -/
def packedWitness (data i : Nat) : Fin 2048 × Nat :=
  let n := (data >>> (22 * i)) % (2^22)
  (⟨n % 2048, Nat.mod_lt _ (by decide)⟩, n / 2048)

/-- Check the factor, the row index, and the literal product equation. -/
def indexedTest (t : Fin 18) (j : Fin 38) (k : Fin 32) (e : Nat)
    (rs : Nat → Row) (size : Nat) (w : Fin 2048 × Nat) : Bool :=
  decide (w.1 ∈ factorIndices t) && decide (w.2 < size) &&
    sameBase (row (wordCode j (sylowRepresentatives t j k) e, 0))
      (fastNormalForm w.1 * row (rs w.2))

/-- Every certified indexed row is one of the original rows. -/
theorem indexedRow_mem (t : Fin 18) (rs : Nat → Row) (size : Nat)
    (h : List.ofFn (fun i : Fin size => rs i) = rows t)
    (i : Nat) (hi : i < size) : rs i ∈ rows t := by
  rw [← h]
  exact List.mem_ofFn.mpr ⟨⟨i, hi⟩, rfl⟩

/-- Read one row from a bounded block of 32 original rows. -/
def rowAt {n : Nat} [NeZero n] (chunks : Fin n → Nat) (i : Nat) : Row :=
  packedRow (chunks ⟨i / 32 % n, Nat.mod_lt _ (NeZero.pos n)⟩) (i % 32)

/-- Bounded equalities with slices of the original list certify every lookup. -/
theorem rowAt_mem {n : Nat} [NeZero n] (t : Fin 18) (chunks : Fin n → Nat)
    (h : ∀ b : Fin n, List.ofFn (fun i : Fin 32 => packedRow (chunks b) i) =
      ((rows t).drop (32 * b.val)).take 32)
    (i : Nat) (hi : i < 32 * n) : rowAt chunks i ∈ rows t := by
  have hb : i / 32 < n := by omega
  have he : (⟨i / 32 % n, Nat.mod_lt _ (NeZero.pos n)⟩ : Fin n) =
      ⟨i / 32, hb⟩ := Fin.ext (Nat.mod_eq_of_lt hb)
  simp only [rowAt, he]
  apply List.mem_of_mem_drop (i := 32 * (i / 32))
  apply List.mem_of_mem_take (i := 32)
  rw [← h ⟨i / 32, hb⟩]
  exact List.mem_ofFn.mpr ⟨⟨i % 32, Nat.mod_lt _ (by decide)⟩, rfl⟩

/-- An indexed certificate discharges the actual rotation-cover conclusion. -/
theorem indexedTest_sound (t : Fin 18) (j : Fin 38) (k : Fin 32) (e : Nat)
    (rs : Nat → Row) (size : Nat) (w : Fin 2048 × Nat)
    (hrows : ∀ i, i < size → rs i ∈ rows t)
    (h : indexedTest t j k e rs size w = true) :
    ∃ q ∈ factors t, ∃ r ∈ rows t,
      conjugate j (atlas1600SylowTwoNormalForm (sylowRepresentatives t j k) *
        rotation j ^ e) = q * rowElement r := by
  simp only [indexedTest, Bool.and_eq_true, decide_eq_true_eq] at h
  apply rotationTest_sound t j k e (w.1, rs w.2)
  simp only [rotationTest, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨h.1.1, hrows w.2 h.1.2⟩, h.2⟩

/-- Four consecutive representatives in one of eight bounded batches. -/
def blockIndex (b : Fin 8) (i : Fin 4) : Fin 32 :=
  ⟨4 * b.val + i.val, by omega⟩

/-- Assemble bounded checks without repeating any finite calculation. -/
theorem all_blocks (P : Fin 32 → Prop)
    (h : ∀ b : Fin 8, ∀ i : Fin 4, P (blockIndex b i)) (k : Fin 32) : P k := by
  have hk : blockIndex ⟨k.val / 4, by omega⟩ ⟨k.val % 4, by omega⟩ = k := by
    apply Fin.ext
    simp only [blockIndex, Fin.val_mk]
    omega
  rw [← hk]
  exact h _ _

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.Rotations
