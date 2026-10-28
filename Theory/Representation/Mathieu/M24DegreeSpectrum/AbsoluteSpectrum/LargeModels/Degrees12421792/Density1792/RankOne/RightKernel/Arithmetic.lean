module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.Arithmetic

/-!
# Bounded checks for the degree-1792 right kernel

A certified monomial row reads one input coordinate by division. Other rows
use the published binary parity fold. The soundness theorem recovers exactly
`RankOneCertificate.checkAction`, hence the original left action on columns.
Range composition combines checked blocks without repeating their arithmetic.
The concrete consumers are the action certificates beside this module.
See `source/README.md` for the literal ATLAS data and measured checks.
-/

@[expose] public section
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792
open Density1792.RankOneCertificate Thompson.BinaryMatrix Matrix
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RightKernelCertificate

def checkCodes : List Nat → List Nat → Bool
  | [], [] => true
  | r :: rs, c :: cs => (c == 0 || (c - 1 < 1792 && r == 2^(c-1))) && checkCodes rs cs
  | _, _ => false

def rowValue (u r c : Nat) : Bool :=
  if c = 0 then (parity1792 (r &&& u)).testBit 0 else (u / r % 2 == 1)

def check (u v : Nat) : List Nat → List Nat → Bool
  | [], [] => true
  | r :: rs, c :: cs => (rowValue u r c == (v % 2 == 1)) && check u (v / 2) rs cs
  | _, _ => false

lemma mono_dot (u j : Nat) (hj : j < 1792) :
    bit (parity1792 ((2^j) &&& u)) 0 = bit u j := by
  rw [dot_spec]
  have hv : vector (2^j) = Pi.single (⟨j,hj⟩ : Fin 1792) 1 := by
    ext i
    simp [vector, bit, Nat.testBit_two_pow, Pi.single_apply, Fin.ext_iff, eq_comm]
  rw [hv, single_dotProduct]
  simp [vector]

lemma rowValue_eq (u r c : Nat)
    (h : (c == 0 || (decide (c - 1 < 1792) && r == 2^(c-1))) = true) :
    rowValue u r c = (parity1792 (r &&& u)).testBit 0 := by
  by_cases hc : c = 0
  · simp [rowValue, hc]
  · simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨hj, hr⟩ := h.resolve_left hc
    subst r
    have hh := mono_dot u (c-1) hj
    have hb : (parity1792 ((2^(c-1)) &&& u)).testBit 0 = u.testBit (c-1) := by
      cases h₁ : (parity1792 ((2^(c-1)) &&& u)).testBit 0 <;>
        cases h₂ : u.testBit (c-1) <;> simp_all [bit]
    simp [rowValue, hc, hb, Nat.testBit_eq_decide_div_mod_eq, Bool.beq_eq_decide_eq]

lemma check_sound (u v : Nat) (rs cs : List Nat)
    (hc : checkCodes rs cs = true) (h : check u v rs cs = true) :
    checkAction u v rs = true := by
  induction rs generalizing v cs with
  | nil => rfl
  | cons r rs ih =>
    cases cs with
    | nil => simp [checkCodes] at hc
    | cons c cs =>
      simp only [checkCodes, Bool.and_eq_true] at hc
      simp only [check, Bool.and_eq_true, beq_iff_eq] at h
      have hv : (v % 2 == 1) = v.testBit 0 := by
        simp [Nat.testBit_eq_decide_div_mod_eq, Bool.beq_eq_decide_eq]
      rw [rowValue_eq u r c hc.1, hv] at h
      simp only [checkAction, Bool.and_eq_true, beq_iff_eq]
      exact ⟨h.1, ih (v / 2) cs hc.2 h.2⟩
lemma checkCodes_take (n : Nat) (rs cs : List Nat) (h : checkCodes rs cs = true) :
    checkCodes (rs.take n) (cs.take n) = true := by
  induction n generalizing rs cs with
  | zero => rfl
  | succ n ih =>
    cases rs <;> cases cs <;> simp_all [checkCodes]

lemma checkCodes_drop (n : Nat) (rs cs : List Nat) (h : checkCodes rs cs = true) :
    checkCodes (rs.drop n) (cs.drop n) = true := by
  induction n generalizing rs cs with
  | zero => exact h
  | succ n ih =>
    cases rs <;> cases cs <;> simp_all [checkCodes]

lemma checkAction_append (u v : Nat) (rs ss : List Nat) :
    checkAction u v (rs ++ ss) =
      (checkAction u v rs && checkAction u (v / 2^rs.length) ss) := by
  induction rs generalizing v with
  | nil => simp [checkAction]
  | cons r rs ih =>
    simp [checkAction, ih, Bool.and_assoc, Nat.div_div_eq_div_mul, pow_succ']

def actionRange (u v : Nat) (rs : List Nat) (start count : Nat) : Bool :=
  checkAction u (v / 2^start) ((rs.drop start).take count)

lemma actionRange_join (u v : Nat) (rs : List Nat) (start a b : Nat)
    (hlen : start + a ≤ rs.length)
    (h₁ : actionRange u v rs start a = true)
    (h₂ : actionRange u v rs (start+a) b = true) :
    actionRange u v rs start (a+b) = true := by
  have ha : a ≤ (rs.drop start).length := by simp only [List.length_drop]; omega
  simp only [actionRange, List.take_add, checkAction_append,
    List.length_take_of_le ha, Nat.div_div_eq_div_mul, ← pow_add,
    List.drop_drop] at *
  simp only [Bool.and_eq_true]
  exact ⟨h₁, h₂⟩

lemma actionRange_of_check (u v : Nat) (rs cs : List Nat) (start count : Nat)
    (hc : checkCodes rs cs = true)
    (h : check u (v / 2^start) ((rs.drop start).take count) ((cs.drop start).take count) = true) :
    actionRange u v rs start count = true :=
  check_sound u (v / 2^start) _ _
    (checkCodes_take count _ _ (checkCodes_drop start rs cs hc)) h

lemma checkAction_of_range (u v : Nat) (rs : List Nat) (n : Nat) (hn : rs.length = n)
    (h : actionRange u v rs 0 n = true) : checkAction u v rs = true := by
  simpa [actionRange, ← hn] using h
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RightKernelCertificate
