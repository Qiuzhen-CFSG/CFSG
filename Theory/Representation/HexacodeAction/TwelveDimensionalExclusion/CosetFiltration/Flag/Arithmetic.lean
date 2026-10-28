module
public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.Data

/-!
# Packed arithmetic for F₄ columns

The two natural numbers store the coefficients of 1 and omega. Bitwise XOR
models addition, and multiplication by omega sends (a,b) to (b,a+b).
The decoding lemmas prove these operations agree with the published `entry`
map, allowing kernel-checked integer equalities to certify matrix identities
without reducing thousands of operations in the quadratic-field implementation.

Application: the central coset filtration for Aschbacher–Smith K.1.3,
printed p.453 / PDF p.464. The witness provenance is in `../source/README.md`.
-/

@[expose] public section
namespace Representation.Hexacode.TwelveDimensional.CosetCertificate.Flag

abbrev Packed := ℕ × ℕ

def code (p : Packed) (i : ℕ) : Fin 4 :=
  if p.2.testBit i then (if p.1.testBit i then 3 else 2)
  else (if p.1.testBit i then 1 else 0)

def pxor (p q : Packed) : Packed := (p.1 ^^^ q.1, p.2 ^^^ q.2)

def scale (a : Fin 4) (p : Packed) : Packed :=
  match a.val with
  | 0 => (0, 0)
  | 1 => p
  | 2 => (p.2, p.1 ^^^ p.2)
  | _ => (p.1 ^^^ p.2, p.1)

theorem decode_xor (p q : Packed) (i : ℕ) :
    entry (code (pxor p q) i) = entry (code p i) + entry (code q i) := by
  simp only [code, pxor, Nat.testBit_xor]
  cases p.1.testBit i <;> cases p.2.testBit i <;>
    cases q.1.testBit i <;> cases q.2.testBit i <;> decide +kernel

theorem decode_zero (i : ℕ) : entry (code (0, 0) i) = 0 := by
  simp [code, entry]

theorem decode_scale (a : Fin 4) (p : Packed) (i : ℕ) :
    entry (code (scale a p) i) = entry a * entry (code p i) := by
  fin_cases a <;> simp only [scale, code, Nat.testBit_xor, Nat.zero_testBit]
  all_goals cases p.1.testBit i <;> cases p.2.testBit i <;> decide +kernel

def xorList : List Packed → Packed
  | [] => (0, 0)
  | p :: ps => pxor p (xorList ps)

theorem decode_xorList (ps : List Packed) (i : ℕ) :
    entry (code (xorList ps) i) = (ps.map fun p => entry (code p i)).sum := by
  induction ps with
  | nil => exact decode_zero i
  | cons p ps ih => simp only [xorList, decode_xor, ih, List.map_cons, List.sum_cons]

def combine {n : ℕ} (c : Fin n → Packed) (v : Fin n → Fin 4) : Packed :=
  xorList (List.ofFn fun j => scale (v j) (c j))

theorem decode_combine {n : ℕ} (c : Fin n → Packed) (v : Fin n → Fin 4) (i : ℕ) :
    entry (code (combine c v) i) = ∑ j, entry (code (c j) i) * entry (v j) := by
  rw [combine, decode_xorList, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.comp_apply, decode_scale, mul_comm]

theorem decode_power (i j : ℕ) :
    entry (code (2 ^ j, 0) i) = if j = i then 1 else 0 := by
  simp only [code, Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte, Nat.testBit_two_pow]
  by_cases h : j = i <;> simp [h, entry]

def pack {n : ℕ} (v : Fin n → Fin 4) : Packed :=
  combine (fun j => (2 ^ j.val, 0)) v

theorem decode_pack {n : ℕ} (v : Fin n → Fin 4) (i : Fin n) :
    entry (code (pack v) i.val) = entry (v i) := by
  rw [pack, decode_combine]
  simp only [decode_power, Fin.val_inj, ite_mul, one_mul, zero_mul]
  simp

def codeMul (a b : Fin 4) : Fin 4 :=
  (![![0,0,0,0],![0,1,2,3],![0,2,3,1],![0,3,1,2]] : Fin 4 → Fin 4 → Fin 4) a b

theorem decode_mul : ∀ a b, entry (codeMul a b) = entry a * entry b := by
  decide +kernel

end Representation.Hexacode.TwelveDimensional.CosetCertificate.Flag
