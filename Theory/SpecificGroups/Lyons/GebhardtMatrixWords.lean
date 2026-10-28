module

public import Theory.SpecificGroups.Lyons.GebhardtMatrixRealizationSetup
public import Theory.SpecificGroups.Lyons.GebhardtMatrixRecoveryWords

/-!
# Explicit words for the Sims–Gebhardt generators

These four words specify candidate images of `a,b,c,d` in the exact ATLAS
local pair. They were found by enumerating the degree-3906 action of the
16-relator local presentation and expressing its generators in a pair
of orders 2 and 3. The outer word was found in the centralizer of the fourth
power of `a`, using its 55-dimensional constituent to search a group of 960
matrices. All 25 literal relations were then checked numerically on the exact
111-dimensional matrices. That computation is discovery data, not a kernel
proof or a claim that the presentation is sufficient.

The ambient recovery words are in `GebhardtMatrixRecoveryWords`. Together these
define concrete `WordData`. No `WordCertificate` is asserted here: numerical
checks of the matrix identities are not kernel proofs. See
`GebhardtMatrixSource/README.md`.

Source: V. Gebhardt, "Two Short Presentations for Lyons' Sporadic Simple
Group", Experimental Mathematics 9 (2000), 333–338, Section 3B.
-/

namespace Lyons.Gebhardt.MatrixRealization
@[expose] public section

/-- Signed letters for either matrix pair; `false` selects its first member. -/
def pairLetter : Char → FreeGroup Bool
  | 'x' => FreeGroup.of false
  | 'X' => (FreeGroup.of false)⁻¹
  | 'y' => FreeGroup.of true
  | 'Y' => (FreeGroup.of true)⁻¹
  | _ => 1

/-- Evaluate a written signed word in the free group on the pair. -/
def pairWord (s : String) : FreeGroup Bool := (s.toList.map pairLetter).prod

/-- Concrete local word strings, in the order `a,b,c,d`. -/
def localWordStrings : Fin 4 → String
  | 0 => "XyxYxyxYxyxYYXyXYXYXyXyXYXyXYXYXyXyXYXyXYXyXYXYXyXyXYXYXYYXyXyXYXYXyXYXyXyXYXYXyXYXyXyXYXYXyXyXYXYxyxYxyxyxYxyxYxYxyxYYXYXyXyXYXyXYXYXyXyXYXyXYXYXyXyXYXYXyXYXYXYXyXYXyXyXYXyXyXYXyXYXyXyXYXYY"
  | 1 => "yyxyxyyxyxyyxYxyxYxyxYxyxYxYxyxYxyxYxYxYxYxyxyxYxYxyxYxyxYxyxyxYxyxYXYXyXyXYXYXyXYXyXYXyxyxYxyxyxYxyxYxyxyxYxYxyxYxyxYxyxYxYxyxYxyxyxYxYXyXYXYXyXyXYXyXYXYXyXyXYXyXyXYXyXYXyXYYXyXYXyXyXYXYXyXyXYXyXYXYXyXYxyxyxYxyxyxYxyxYxyxYxYxyxyxYxyxYxYxyxYxy"
  | 2 => "yxyxYxyxyxYxyxYxyxyxYxYxyxYxyxYxYxYxyxyxYxyxYxyxYxyxyxYxyxYxyxyxYxYxyxYYXyXyXYXyXYXYXyXYXyXyXYXyXYXyXYXyxYxyxYxyxYxYxyxyxYxyxYxYxyxYxyxYxyxyxYxyxyxYxyyXYXYXyXyXYXyXyXYXyXYXYXYYX"
  | _ => "YXYXYxyxyxYxyxYxYxyxyxYxyxYxyxYYXYXyXyXYXyXYXYXyXYXyXYXyXYXyXYXYXyXYXyxyxYxYxyxYxyxYxyxYxyxYxYxyxYxyxYxyxYxYxyyXYXyXYXYXyXYXyXyXYXyXYXyXyXYXyXYXYXyXyXYXYXyXyXYXyXYXyXYXyXYXyXYXyXYYXYXyXYXYXyXYXyXYXyXYXyXYXyXYYXYXYXY"

/-- Candidate images of the four local generators, as explicit free words. -/
def localWords (i : Fin 4) : FreeGroup Bool := pairWord (localWordStrings i)

-- Generated outer-word definitions: see GebhardtMatrixSource/GenerateWords.py.

/-- A concrete ambient word whose matrix is the fourth power of the local `a`. -/
def centralizerInvolutionWord : FreeGroup Bool :=
  let u := pairWord "xyxyyy" ^ 7
  u * FreeGroup.of false * u⁻¹

/-- A pure word expression used to record the centralizer search compactly.
The parameter is just an exponent input; no element-order claim is assumed. -/
def centralizerSearchWord (sample : FreeGroup Bool) (n : Nat) : FreeGroup Bool :=
  let t := centralizerInvolutionWord
  let h := t * sample⁻¹ * t * sample
  (if n % 2 = 1 then sample else 1) * h ^ (n / 2)

/-- The twelve explicit words used in the numerical centralizer search. -/
def centralizerWords : Fin 12 → FreeGroup Bool
  | 0 => centralizerSearchWord (pairWord "xxxyyxxxyyxxyyxxxxyxyyyxxxyxxx") 67
  | 1 => centralizerSearchWord (pairWord "xxyyxxxxyxxyyxyxyyyxyxyxxxxxxy") 67
  | 2 => centralizerSearchWord (pairWord "xyyxxxxyxyxxxxyyxyxxxyyxxyxxxy") 6
  | 3 => centralizerSearchWord (pairWord "xyyyyxxxyxxxxyyyyxxxxyxxyxxyyx") 31
  | 4 => centralizerSearchWord (pairWord "xyxyyyxxxxxxyyyxxyyyxyxyxxxxxx") 31
  | 5 => centralizerSearchWord (pairWord "xyyxxxxyyyyxxxyyxxxyxxxyxyyxyy") 67
  | 6 => centralizerSearchWord (pairWord "xyyyyxyxyxyyxxyyxyyyxyxxxyyyxy") 12
  | 7 => centralizerSearchWord (pairWord "xxxyxyyxyxyxyxxyyxxyxyyyyxyyyx") 12
  | 8 => centralizerSearchWord (pairWord "xxxxyxyyxyyyxyxyyxxxyxxxxxxxxx") 31
  | 9 => centralizerSearchWord (pairWord "yxxyxyyyxyxyyxyyxxyyyxxyyxyxyy") 15
  | 10 => centralizerSearchWord (pairWord "xxxxyxxyyxyyxxxyyxyxxxyxxyxxxx") 31
  | _ => centralizerSearchWord (pairWord "xyxyyxyxxxyxyyxxxyxxyxxyyxxxyx") 67

/-- Explicit candidate image of `z` in the ambient pair. All 25 source relations
pass numerical checks with `localWords`; kernel certification is separate. -/
def outerWord : FreeGroup Bool :=
  centralizerWords 10 ^ (-1 : ℤ) *
    centralizerWords 1 ^ (2 : ℤ) *
    centralizerWords 10 ^ (-3 : ℤ) *
    centralizerWords 1 ^ (-1 : ℤ) *
    centralizerWords 6 ^ (1 : ℤ) *
    centralizerWords 10 ^ (1 : ℤ) *
    centralizerWords 9 ^ (1 : ℤ) *
    centralizerWords 0 ^ (2 : ℤ) *
    centralizerWords 1 ^ (-1 : ℤ) *
    centralizerWords 8 ^ (1 : ℤ) *
    centralizerWords 6 ^ (1 : ℤ) *
    centralizerWords 0 ^ (1 : ℤ) *
    centralizerWords 1 ^ (1 : ℤ) *
    centralizerWords 11 ^ (1 : ℤ)

-- Concrete WordData assembly.

/-- The explicit Sims–Gebhardt correspondence and ambient recovery words. -/
def wordData : WordData where
  localWords := localWords
  outerWord := outerWord
  recoverA := recoverA
  recoverB := recoverB

end
end Lyons.Gebhardt.MatrixRealization
