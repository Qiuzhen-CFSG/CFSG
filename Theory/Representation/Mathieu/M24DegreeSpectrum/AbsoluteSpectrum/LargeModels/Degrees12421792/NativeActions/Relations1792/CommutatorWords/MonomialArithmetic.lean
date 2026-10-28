module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic

/-!
# Sparse paths through the original row matrices

A partial map records one-based destinations of monomial rows in base 2048;
zero means that the row is unspecified. `checkMap_sound` verifies each claimed
row against the original row list. Following a positive word through such
rows then evaluates the actual matrix word, without a dense product.

`rowWord_eq_of_maps` also checks the proposed output table. Its consumer in
`MonomialRows` proves 1007 rows of source word 3 and 559 rows of source word 4.
The other rows and both order equations remain separate obligations.
Source: ATLAS M24G1-P1 and the degree-1792 row matrices; see `source/README.md`.
-/

@[expose] public section
open scoped BigOperators
open Thompson.BinaryMatrix
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.MonomialArithmetic

def destination (code i : Nat) : Nat := code / 2048 ^ i % 2048

def checkMap : List Nat → Nat → Bool
  | [], _ => true
  | r :: rs, code =>
      ((code % 2048 == 0) || (r == 2 ^ (code % 2048 - 1))) &&
        checkMap rs (code / 2048)

theorem checkMap_sound (rs : List Nat) (code : Nat) (h : checkMap rs code = true)
    (i : Nat) (hi : i < rs.length) (hd : destination code i ≠ 0) :
    rs[i]! = 2 ^ (destination code i - 1) := by
  induction rs generalizing code i with
  | nil => simp at hi
  | cons r rs ih =>
    simp only [checkMap, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    cases i with
    | zero =>
      simp only [destination, pow_zero, Nat.div_one] at hd ⊢
      rcases h.1 with hzero | hr
      · exact (hd hzero).elim
      · simpa using hr
    | succ i =>
      have he : destination (code / 2048) i = destination code (i+1) := by
        simp [destination, pow_succ', Nat.div_div_eq_div_mul]
      simpa only [List.getElem!_cons_succ, he] using
        ih (code / 2048) h.2 i (by simpa using hi) (by simpa only [he] using hd)

theorem decode_row_of_map {n : Nat} (rs : Array Nat) (code : Nat)
    (h : checkMap rs.toList code = true) (hs : rs.size = n)
    (i j : Fin n) (hd : destination code i.val = j.val + 1) :
    decode n rs i = Pi.single j 1 := by
  have hx := checkMap_sound rs.toList code h i.val (by simp [hs])
    (by rw [hd]; omega)
  simp only [hd, Nat.add_sub_cancel] at hx
  have hx' : rs[i.val]! = 2 ^ j.val := by simpa [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?] using hx
  funext k
  simp [decode, hx', bit, Nat.testBit_two_pow, Pi.single_apply, Fin.ext_iff, eq_comm]

def rowWord {n : Nat} (A B : Matrix (Fin n) (Fin n) (ZMod 2)) :
    List Bool → Matrix (Fin n) (Fin n) (ZMod 2)
  | [] => 1
  | b :: bs => (if b then B else A) * rowWord A B bs

def follow (n ca cb : Nat) : List Bool → Nat → Option Nat
  | [], i => some i
  | b :: bs, i =>
      let d := destination (if b then cb else ca) i
      if d = 0 ∨ n < d then none else follow n ca cb bs (d - 1)

theorem mul_row_single {n : Nat} (A B : Matrix (Fin n) (Fin n) (ZMod 2))
    (i k : Fin n) (h : A i = Pi.single k 1) : (A * B) i = B k := by
  funext j
  simp [Matrix.mul_apply, congrFun h, Pi.single_apply]

theorem rowWord_of_follow {n : Nat} (A B : Matrix (Fin n) (Fin n) (ZMod 2))
    (ca cb : Nat)
    (ha : ∀ i j : Fin n, destination ca i.val = j.val + 1 → A i = Pi.single j 1)
    (hb : ∀ i j : Fin n, destination cb i.val = j.val + 1 → B i = Pi.single j 1)
    (ws : List Bool) (i j : Fin n) (h : follow n ca cb ws i.val = some j.val) :
    rowWord A B ws i = Pi.single j 1 := by
  induction ws generalizing i with
  | nil =>
    simp only [follow, Option.some.injEq] at h
    have hij : i = j := Fin.ext h
    subst j
    funext k
    simp [rowWord, Matrix.one_apply, Pi.single_apply, eq_comm]
  | cons b bs ih =>
    let d := destination (if b then cb else ca) i.val
    change (if d = 0 ∨ n < d then none else follow n ca cb bs (d - 1)) = some j.val at h
    by_cases hd : d = 0 ∨ n < d
    · simp only [if_pos hd] at h
      contradiction
    · simp only [if_neg hd] at h
      have hd0 : d ≠ 0 := fun hh => hd (Or.inl hh)
      have hbound : d ≤ n := by omega
      let k : Fin n := ⟨d - 1, by omega⟩
      have hk : destination (if b then cb else ca) i.val = k.val + 1 := by
        change d = d - 1 + 1
        omega
      rw [rowWord, mul_row_single _ _ i k]
      · exact ih k h
      · cases b
        · exact ha i k hk
        · exact hb i k hk

theorem follow_lt (n ca cb : Nat) (ws : List Bool) (i j : Nat)
    (hi : i < n) (h : follow n ca cb ws i = some j) : j < n := by
  induction ws generalizing i with
  | nil =>
    simp only [follow, Option.some.injEq] at h
    exact h ▸ hi
  | cons b bs ih =>
    let d := destination (if b then cb else ca) i
    change (if d = 0 ∨ n < d then none else follow n ca cb bs (d-1)) = some j at h
    by_cases hd : d = 0 ∨ n < d
    · simp only [if_pos hd] at h
      contradiction
    · simp only [if_neg hd] at h
      exact ih (d-1) (by omega) h

def checkPaths (n ca cb : Nat) (ws : List Bool) (cm : Nat) : Bool :=
  (List.range n).all fun i =>
    (destination cm i == 0) || (follow n ca cb ws i == some (destination cm i - 1))

theorem checkPaths_sound (n ca cb : Nat) (ws : List Bool) (cm : Nat)
    (h : checkPaths n ca cb ws cm = true) (i : Fin n)
    (hd : destination cm i.val ≠ 0) :
    follow n ca cb ws i.val = some (destination cm i.val - 1) := by
  have hh := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simp only [Bool.or_eq_true, beq_iff_eq] at hh
  exact hh.resolve_left hd

theorem rowWord_eq_of_maps {n : Nat} (a b c : Array Nat)
    (ca cb cc : Nat) (ws : List Bool)
    (ha : checkMap a.toList ca = true) (hb : checkMap b.toList cb = true)
    (hc : checkMap c.toList cc = true)
    (hsa : a.size = n) (hsb : b.size = n) (hsc : c.size = n)
    (hpaths : checkPaths n ca cb ws cc = true)
    (i : Fin n) (hi : destination cc i.val ≠ 0) :
    rowWord (decode n a) (decode n b) ws i = decode n c i := by
  have hp := checkPaths_sound n ca cb ws cc hpaths i hi
  let j : Fin n := ⟨destination cc i.val - 1, follow_lt n ca cb ws _ _ i.isLt hp⟩
  have hj : destination cc i.val = j.val + 1 := by
    dsimp [j]
    omega
  rw [rowWord_of_follow _ _ ca cb
    (decode_row_of_map a ca ha hsa) (decode_row_of_map b cb hb hsb) ws i j hp,
    decode_row_of_map c cc hc hsc i j hj]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.MonomialArithmetic
