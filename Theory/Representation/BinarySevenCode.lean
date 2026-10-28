module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FinCases

/-!
# Binary words of length seven

The even-weight words give the six-dimensional permutation module for `A₇`.
The binary simplex code embeds a three-dimensional space into this module,
with every nonzero word of weight four. We use a systematic encoding: the
second, sixth, and seventh coordinates recover the input. The eight inputs
suffice to check the weight and parity identities by kernel reduction.

This concrete module is used when checking the weight-four subspace argument
in Aschbacher–Smith, *The Classification of Quasithin Groups*, §12.3,
Lemma 12.3.9 (1 March 2004 manuscript, printed p. 810).
-/

namespace BinarySevenCode

/-- The binary permutation space on seven points. -/
public abbrev Word := Fin 7 → ZMod 2

/-- Number of nonzero coordinates. -/
@[expose] public def weight (v : Word) : ℕ :=
  (Finset.univ.filter (fun i => v i ≠ 0)).card

/-- The augmentation submodule of the binary permutation space. -/
public def evenWords : Submodule (ZMod 2) Word :=
  (∑ i : Fin 7, (LinearMap.proj i : Word →ₗ[ZMod 2] ZMod 2)).ker

public theorem mem_evenWords_iff (v : Word) :
    v ∈ evenWords ↔ ∑ i, v i = 0 := by
  simp [evenWords, LinearMap.mem_ker]

/-- The three generators have supports `{1,2,3,4}`, `{3,4,5,6}`, and
`{1,3,5,7}`, with the coordinates numbered from one. -/
@[expose] public def encode : (Fin 3 → ZMod 2) →ₗ[ZMod 2] Word where
  toFun x := ![x 0 + x 2, x 0, x 0 + x 1 + x 2, x 0 + x 1,
    x 1 + x 2, x 1, x 2]
  map_add' x y := by
    ext i
    fin_cases i <;> simp [add_assoc, add_left_comm, add_comm]
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [mul_add]

public theorem encode_injective : Function.Injective encode := by
  intro x y h
  have h0 := congrFun h 1
  have h1 := congrFun h 5
  have h2 := congrFun h 6
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

public theorem weight_encode (x : Fin 3 → ZMod 2) (hx : x ≠ 0) :
    weight (encode x) = 4 := by
  exact (by decide : ∀ y : Fin 3 → ZMod 2, y ≠ 0 → weight (encode y) = 4) x hx

public theorem encode_mem_evenWords (x : Fin 3 → ZMod 2) : encode x ∈ evenWords := by
  rw [mem_evenWords_iff]
  exact (by decide : ∀ y : Fin 3 → ZMod 2, ∑ i, encode y i = 0) x

/-- The binary `[7,3,4]` simplex code. -/
public def simplexCode : Submodule (ZMod 2) Word := encode.range

public theorem mem_simplexCode_iff (v : Word) :
    v ∈ simplexCode ↔ ∃ x, encode x = v := Iff.rfl

public theorem finrank_simplexCode : Module.finrank (ZMod 2) simplexCode = 3 := by
  rw [simplexCode, LinearMap.finrank_range_of_inj encode_injective]
  exact Module.finrank_fin_fun (ZMod 2)

public theorem simplexCode_le_evenWords : simplexCode ≤ evenWords := by
  rintro v ⟨x, rfl⟩
  exact encode_mem_evenWords x

public theorem weight_of_mem_simplexCode {v : Word} (hv : v ∈ simplexCode)
    (hne : v ≠ 0) : weight v = 4 := by
  obtain ⟨x, rfl⟩ := hv
  apply weight_encode
  intro hx
  apply hne
  rw [hx, map_zero]

set_option maxRecDepth 4096 in
/-- Nonzero even words have precisely the three weights used in the natural
`A₇`-module orbit calculation. -/
public theorem weight_of_mem_evenWords {v : Word} (hv : v ∈ evenWords)
    (hne : v ≠ 0) : weight v = 2 ∨ weight v = 4 ∨ weight v = 6 := by
  rw [mem_evenWords_iff] at hv
  exact (by decide : ∀ w : Word, (∑ i, w i = 0) → w ≠ 0 →
    weight w = 2 ∨ weight w = 4 ∨ weight w = 6) v hv hne

/-- Different coordinates are distinguished by some word of the simplex code. -/
public theorem coordinates_separated (i j : Fin 7)
    (h : ∀ v ∈ simplexCode, v i = v j) : i = j := by
  have hx : ∀ x : Fin 3 → ZMod 2, encode x i = encode x j :=
    fun x => h (encode x) ⟨x, rfl⟩
  exact (by decide : ∀ a b : Fin 7,
    (∀ x : Fin 3 → ZMod 2, encode x a = encode x b) → a = b) i j hx

/-- The pointwise stabilizer of the simplex code in the symmetric group is
trivial. This distinguishes it from the weight-four plane. -/
public theorem perm_eq_one_of_fixes_simplexCode (p : Equiv.Perm (Fin 7))
    (h : ∀ v ∈ simplexCode, ∀ i, v (p i) = v i) : p = 1 := by
  apply Equiv.ext
  intro i
  exact coordinates_separated (p i) i (fun v hv => h v hv i)

end BinarySevenCode
