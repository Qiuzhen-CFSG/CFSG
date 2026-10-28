module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBound.Maps

/-!
# Word evaluation for the HS conjugate certificate

A bounded base-four word decoder gives actual elements of the HS carrier.
Forward and inverse point evaluation agree with those elements. The integer
signature records the images of points 0 through 4 in base 100.

Source: ATLAS HSG1-p100B0; Aschbacher–Smith 16.1.5(10), printed p.1172;
GLS3, Table 5.3m. No orbit size or centralizer shape is assumed.
-/

@[expose] public section
open Theory.GroupTheory Sporadic.LeechRelated.HS
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBoundCertificate
open Certificate
def digit (code : ℕ) : Fin 3 := ⟨(code % 4 - 1) % 3, Nat.mod_lt _ (by decide)⟩
def word : ℕ → ℕ → List (Fin 3)
  | 0, _ => []
  | n + 1, code => if code = 0 then [] else digit code :: word n (code >>> 2)
def wordValue : ℕ → ℕ → Fin 100 → Fin 100
  | 0, _, p => p
  | n + 1, code, p => if code = 0 then p else
      letterValue (digit code) (wordValue n (code >>> 2) p)
def inverseWordValue : ℕ → ℕ → Fin 100 → Fin 100
  | 0, _, p => p
  | n + 1, code, p => if code = 0 then p else
      inverseWordValue n (code >>> 2) (inverseLetterValue (digit code) p)

theorem wordValue_spec (n code : ℕ) (p : Fin 100) :
    wordValue n code p = inclusion (evalWord ambientLetter (word n code)) p := by
  induction n generalizing code p with
  | zero => rfl
  | succ n ih =>
    by_cases h : code = 0
    · simp only [wordValue, word, h, ↓reduceIte]; rfl
    · simp only [wordValue, word, h, ↓reduceIte, evalWord, map_mul,
        Equiv.Perm.mul_apply, letterValue_spec, ih]

theorem inverseWordValue_spec (n code : ℕ) (p : Fin 100) :
    inverseWordValue n code p = inclusion (evalWord ambientLetter (word n code))⁻¹ p := by
  induction n generalizing code p with
  | zero => rfl
  | succ n ih =>
    by_cases h : code = 0
    · simp only [inverseWordValue, word, h, ↓reduceIte]; rfl
    · simp only [inverseWordValue, word, h, ↓reduceIte, evalWord, mul_inv_rev,
        map_mul, Equiv.Perm.mul_apply, inverseLetterValue_spec, ih]

def conjugate (code : ℕ) : Carrier :=
  let g := evalWord ambientLetter (word 19 code)
  g⁻¹ * t * g

def conjugateValue (code : ℕ) (p : Fin 100) : Fin 100 :=
  inverseWordValue 19 code (baseValue (wordValue 19 code p))

theorem conjugateValue_spec (code : ℕ) (p : Fin 100) :
    conjugateValue code p = inclusion (conjugate code) p := by
  simp only [conjugateValue, inverseWordValue_spec, baseValue_spec, wordValue_spec,
    conjugate, map_mul, Equiv.Perm.mul_apply]

def signature (v : Fin 100 → Fin 100) : ℕ :=
  ((((v 0).val * 100 + (v 1).val) * 100 + (v 2).val) * 100 + (v 3).val) * 100 +
    (v 4).val

def codeSignature (code : ℕ) : ℕ := signature (conjugateValue code)

theorem codeSignature_spec (code : ℕ) :
    codeSignature code = signature (inclusion (conjugate code)) := by
  simp only [codeSignature, signature, conjugateValue_spec]

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductBoundCertificate
