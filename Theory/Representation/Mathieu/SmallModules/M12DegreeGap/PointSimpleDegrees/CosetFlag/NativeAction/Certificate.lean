module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.CosetFlag.NativeAction.Tables
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.Witness

/-!
# Kernel certificate for the native eleven-coset action

The packed words and action indices are checked against the entire shared input
arrays. A generic extraction lemma recovers each literal entry. The finite check
then verifies every generator/word identity on eleven points, with correction
exponents below eleven. Its numeric evaluator is identified with the native M₁₁
action in the parent `NativeAction` module.

Packing makes input lookup inexpensive; fused word evaluation avoids building
intermediate lists. Every finite assertion uses `decide +kernel`.
Source context: James, J. Algebra 27 (1973), 57–111; `../../source/README.md`.
-/

@[expose] public section
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag.NativeActionCertificate

def unpack {α : Type} (width : ℕ) (f : ℕ → α) : ℕ → ℕ → List α
  | 0, _ => []
  | n+1, c => f (c % 2^width) :: unpack width f n (c >>> width)

def decodeWord : ℕ → ℕ → List (Fin 2)
  | 0, _ => []
  | n+1, c => if c ≤ 1 then [] else Fin.ofNat 2 c :: decodeWord n (c/2)

def digit (width c i : ℕ) : ℕ := (c >>> (width*i)) % 2^width






def wordAt (j : ℕ) := decodeWord 24 (digit 24 words j)
def leftAt (s : Fin 2) (j : ℕ) : Fin 720 :=
  Fin.ofNat 720 (digit 10 (if s = 0 then left0 else left1) j)
def correction (s : Fin 2) (j : ℕ) : ℕ :=
  digit 4 (if s = 0 then correction0 else correction1) j

def generatorPoint (s : Fin 2) (x : ℕ) : ℕ :=
  ((if s = 0 then 2788883970580 else 11138886763840) >>> (4*x)) % 16

def wordPoint : List (Fin 2) → ℕ → ℕ
  | [], x => x
  | s :: w, x => generatorPoint s (wordPoint w x)

def powerPoint : ℕ → ℕ → ℕ
  | 0, x => x
  | n+1, x => generatorPoint 0 (generatorPoint 1 (powerPoint n x))

theorem words_match : Witness.wordData.toList = unpack 24 (decodeWord 24) 720 words := by
  decide +kernel

theorem left_match : ∀ s : Fin 2, Witness.leftAction[s.val]!.toList =
    unpack 10 (Fin.ofNat 720) 720 (if s = 0 then left0 else left1) := by
  decide +kernel

theorem unpack_get {α : Type} [Inhabited α] (width : ℕ) (f : ℕ → α)
    (n c i : ℕ) (hi : i < n) :
    (unpack width f n c)[i]! = f (digit width c i) := by
  induction n generalizing c i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [unpack, digit]
    | succ i =>
      rw [unpack, List.getElem!_cons_succ, ih _ _ (by omega)]
      simp only [digit, ← Nat.shiftRight_add, Nat.mul_succ, Nat.add_comm]

theorem wordAt_eq (j : Fin 720) : Witness.wordData[j.val]! = wordAt j.val := by
  rw [← Array.getElem!_toList, words_match, unpack_get _ _ _ _ _ j.isLt]
  rfl

theorem leftAt_eq (s : Fin 2) (j : Fin 720) :
    (Witness.leftAction[s.val]!)[j.val]! = leftAt s j.val := by
  rw [← Array.getElem!_toList, left_match s, unpack_get _ _ _ _ _ j.isLt]
  rfl

/-- Fused evaluation avoids constructing a decoded list for each point. -/
def codePoint : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | n+1, c, x => if c ≤ 1 then x else
      generatorPoint (Fin.ofNat 2 c) (codePoint n (c/2) x)

theorem codePoint_eq (n c x : ℕ) :
    wordPoint (decodeWord n c) x = codePoint n c x := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [decodeWord, codePoint]
    split
    · rfl
    · simp only [wordPoint, ih]


def allBelow : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n+1, f => allBelow n f && f n

def entryCheck (s : Fin 2) (j : ℕ) : Bool :=
  decide (correction s j < 11) && allBelow 11 (fun x =>
    generatorPoint s (codePoint 24 (digit 24 words j) x) ==
      codePoint 24 (digit 24 words (leftAt s j).val)
        (powerPoint (correction s j) x))

theorem allBelow_spec (n : ℕ) (f : ℕ → Bool) :
    allBelow n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    rw [allBelow, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, hn⟩ i hi
      by_cases hin : i < n
      · exact h i hin
      · have he : i = n := by omega
        simpa only [he] using hn
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

/-- All 1,440 corrections, on all eleven points, are kernel-checked. -/
theorem checked : allBelow 2 (fun s => allBelow 12 (fun b => allBelow 60 (fun j =>
    entryCheck (Fin.ofNat 2 s) (b*60+j)))) = true := by
  decide +kernel

theorem entryCheck_spec (s : Fin 2) (j : ℕ) :
    entryCheck s j = true ↔ correction s j < 11 ∧ ∀ x < 11,
      generatorPoint s (codePoint 24 (digit 24 words j) x) =
      codePoint 24 (digit 24 words (leftAt s j).val)
        (powerPoint (correction s j) x) := by
  simp only [entryCheck, Bool.and_eq_true, decide_eq_true_eq, allBelow_spec, beq_iff_eq]

/-- The finite certificate, expressed with the decoded words. -/
theorem checked_at (s : Fin 2) (j : Fin 720) :
    correction s j.val < 11 ∧ ∀ x : Fin 11,
    generatorPoint s (wordPoint (wordAt j.val) x.val) =
    wordPoint (wordAt (leftAt s j.val).val)
      (powerPoint (correction s j.val) x.val) := by
  have hs := (allBelow_spec _ _).mp checked s.val s.isLt
  have hb := (allBelow_spec _ _).mp hs (j.val / 60) (by omega)
  have hj := (allBelow_spec _ _).mp hb (j.val % 60) (by omega)
  have he : j.val / 60 * 60 + j.val % 60 = j.val := by omega
  have hse : Fin.ofNat 2 s.val = s := Fin.ext (Nat.mod_eq_of_lt s.isLt)
  rw [hse, he] at hj
  obtain ⟨hc, hp⟩ := (entryCheck_spec s j.val).mp hj
  refine ⟨hc, fun x => ?_⟩
  simpa only [wordAt, codePoint_eq] using hp x.val x.isLt

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag.NativeActionCertificate
