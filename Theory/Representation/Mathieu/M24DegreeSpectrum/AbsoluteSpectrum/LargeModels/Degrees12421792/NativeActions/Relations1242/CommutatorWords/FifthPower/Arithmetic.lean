module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.Arithmetic
/-!
# Verified small lookup tables for binary row multiplication

A table contains all linear combinations of a fixed number of consecutive
rows. Every entry is checked against sequential XOR. Reading successive
coefficient blocks therefore computes exactly the original matrix product.
The concrete consumer is the fifth power of the literal degree-1242 ATLAS
commutator matrix; see `source/README.md`.
-/

open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair
@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Arithmetic
def lookup (bits table i : Nat) : Nat := table / 2 ^ (bits * i) % 2 ^ bits
def fast (width bits : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | a, t :: ts => lookup bits t (a % 2^width) ^^^ fast width bits (a / 2^width) ts

theorem shiftRow_append (a : Nat) (bs cs : List Nat) :
    shiftRow a (bs ++ cs) = shiftRow a bs ^^^ shiftRow (a / 2^bs.length) cs := by
  induction bs generalizing a with
  | nil => simp [shiftRow]
  | cons b bs ih =>
    simp [shiftRow, ih, Nat.xor_assoc, pow_succ', Nat.div_div_eq_div_mul]

theorem row_congr (a b : Nat) (xs : List Nat) (k : Nat)
    (h : ∀ i, i < xs.length → a.testBit (k+i) = b.testBit (k+i)) :
    row a xs k = row b xs k := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero] at h0
    rw [row, row, h0, ih]
    intro i hi
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (i+1) (by simpa using hi)

theorem shiftRow_mod (a : Nat) (bs : List Nat) :
    shiftRow (a % 2^bs.length) bs = shiftRow a bs := by
  rw [shiftRow_eq_row, shiftRow_eq_row]
  apply row_congr
  intro i hi
  simp [Nat.testBit_mod_two_pow, hi]

def tableCheck (width bits : Nat) (bs : List Nat) (t : Nat) : Bool :=
  (bs.length == width) && (List.range (2^width)).all (fun a => lookup bits t a == shiftRow a bs)

def tablesCheck (width bits : Nat) : List (List Nat) → List Nat → Bool
  | [], [] => true
  | bs::bss, t::ts => tableCheck width bits bs t && tablesCheck width bits bss ts
  | _, _ => false

theorem fast_sound (width bits : Nat) (bss : List (List Nat)) (ts : List Nat)
    (h : tablesCheck width bits bss ts = true) (a : Nat) :
    fast width bits a ts = shiftRow a bss.flatten := by
  induction bss generalizing ts a with
  | nil => cases ts <;> simp_all [tablesCheck, fast, shiftRow]
  | cons bs bss ih =>
    cases ts with
    | nil => simp [tablesCheck] at h
    | cons t ts =>
      simp only [tablesCheck, Bool.and_eq_true] at h
      obtain ⟨ht, hr⟩ := h
      simp only [tableCheck, Bool.and_eq_true, beq_iff_eq] at ht
      have he : lookup bits t (a % 2^width) = shiftRow (a % 2^width) bs :=
        of_decide_eq_true (List.all_eq_true.mp ht.2 _ (List.mem_range.mpr
          (Nat.mod_lt _ (Nat.two_pow_pos _))))
      rw [fast, he, ← ht.1, shiftRow_mod, List.flatten_cons, shiftRow_append]
      rw [ht.1, ih ts hr]

def check (width bits : Nat) (ts : List Nat) : List Nat → List Nat → Bool
  | [], [] => true
  | a::as, c::cs => (fast width bits a ts == c) && check width bits ts as cs
  | _, _ => false

theorem check_sound (width bits : Nat) (bss : List (List Nat)) (ts : List Nat)
    (ht : tablesCheck width bits bss ts = true) (as cs : List Nat)
    (h : check width bits ts as cs = true) : checkRows as bss.flatten cs = true := by
  induction as generalizing cs with
  | nil => cases cs <;> simp_all [check, checkRows]
  | cons a as ih =>
    cases cs with
    | nil => simp [check] at h
    | cons c cs =>
      simp only [check, Bool.and_eq_true] at h
      simp only [checkRows, Bool.and_eq_true]
      exact ⟨by simpa only [fast_sound width bits bss ts ht] using h.1, ih cs h.2⟩

theorem product (n width bits : Nat) (as cs : List Nat) (bss : List (List Nat)) (ts : List Nat)
    (ha : as.length = n) (hb : bss.flatten.length = n)
    (ht : tablesCheck width bits bss ts = true) (h : check width bits ts as cs = true) :
    Thompson.BinaryMatrix.decode n as.toArray * Thompson.BinaryMatrix.decode n bss.flatten.toArray =
      Thompson.BinaryMatrix.decode n cs.toArray :=
  product_sound_list n as bss.flatten cs ha hb (check_sound width bits bss ts ht as cs h)


/-- Concatenate separately checked lookup tables. -/
theorem tablesCheck_append (width bits : Nat) (bs cs : List (List Nat)) (ts us : List Nat)
    (h : tablesCheck width bits bs ts = true) (h' : tablesCheck width bits cs us = true) :
    tablesCheck width bits (bs ++ cs) (ts ++ us) = true := by
  induction bs generalizing ts with
  | nil => cases ts <;> simp_all [tablesCheck]
  | cons b bs ih =>
    cases ts with
    | nil => simp [tablesCheck] at h
    | cons t ts =>
      simp only [tablesCheck, Bool.and_eq_true] at h
      simp only [List.cons_append, tablesCheck, Bool.and_eq_true]
      exact ⟨h.1, ih ts h.2⟩

theorem check_append (width bits : Nat) (ts as bs cs ds : List Nat)
    (h : check width bits ts as cs = true) (h' : check width bits ts bs ds = true) :
    check width bits ts (as ++ bs) (cs ++ ds) = true := by
  induction as generalizing cs with
  | nil => cases cs <;> simp_all [check]
  | cons a as ih =>
    cases cs with
    | nil => simp [check] at h
    | cons c cs =>
      simp only [check, Bool.and_eq_true] at h
      simp only [List.cons_append, check, Bool.and_eq_true]
      exact ⟨h.1, ih cs h.2⟩

/-- Check independently compiled blocks of output rows. -/
def chunksCheck (width bits : Nat) (ts : List Nat) : List (List Nat) → List (List Nat) → Bool
  | [], [] => true
  | as::ass, cs::css => check width bits ts as cs && chunksCheck width bits ts ass css
  | _, _ => false

theorem chunksCheck_sound (width bits : Nat) (ts : List Nat) (ass css : List (List Nat))
    (h : chunksCheck width bits ts ass css = true) :
    check width bits ts ass.flatten css.flatten = true := by
  induction ass generalizing css with
  | nil => cases css <;> simp_all [chunksCheck, check]
  | cons as ass ih =>
    cases css with
    | nil => simp [chunksCheck] at h
    | cons cs css =>
      simp only [chunksCheck, Bool.and_eq_true] at h
      exact check_append width bits ts _ _ _ _ h.1 (ih css h.2)

theorem product_chunks (n width bits : Nat) (ass css bss : List (List Nat)) (ts : List Nat)
    (ha : ass.flatten.length = n) (hb : bss.flatten.length = n)
    (ht : tablesCheck width bits bss ts = true) (h : chunksCheck width bits ts ass css = true) :
    Thompson.BinaryMatrix.decode n ass.flatten.toArray *
        Thompson.BinaryMatrix.decode n bss.flatten.toArray =
      Thompson.BinaryMatrix.decode n css.flatten.toArray :=
  product n width bits ass.flatten css.flatten bss ts ha hb ht
    (chunksCheck_sound width bits ts ass css h)
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.FifthPower.Arithmetic
