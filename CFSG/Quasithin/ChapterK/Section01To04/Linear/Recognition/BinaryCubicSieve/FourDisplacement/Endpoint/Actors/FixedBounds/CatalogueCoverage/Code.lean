module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.FixedBounds.Catalogue

/-!
# Binary coordinates for the standard actor extension

The six entries of an upper unitriangular matrix multiply by the usual
triangular formulas. Reversal followed by inverse transpose acts on them by
`graphBits`. These operations use exactly the seven-bit numbering of `CodeModel`.
The small identity and inverse checks below use kernel reduction. Comparison
with the actual adjoint actors and elementary-subgroup enumeration are separate
obligations; no group structure on the codes is assumed here.

Source: Guralnick–Malle, Classification of 2F-modules II, Lemma 4.5 and
Proposition 4.8 step 3A; Aschbacher–Smith K.3.2, printed pp.454–455.
-/

@[expose] public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds
namespace CoverageCode

def encode (b : Fin 6 → ZMod 2) (e : Bool) : Code :=
  Fin.ofNat 128 (2 * (b 0 |>.val) + 4 * (b 1 |>.val) + 8 * (b 2 |>.val) +
    16 * (b 3 |>.val) + 32 * (b 4 |>.val) + 64 * (b 5 |>.val) + e.toNat)

def mulBits (a b : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  ![a 0 + b 0, a 1 + b 1 + a 0 * b 3,
    a 2 + b 2 + a 0 * b 4 + a 1 * b 5,
    a 3 + b 3, a 4 + b 4 + a 3 * b 5, a 5 + b 5]

def inverseBits (b : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  ![b 0, b 1 + b 0 * b 3,
    b 2 + b 0 * b 4 + b 1 * b 5 + b 0 * b 3 * b 5,
    b 3, b 4 + b 3 * b 5, b 5]

def graphBits (b : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  ![b 5, b 4 + b 3 * b 5,
    b 2 + b 0 * b 4 + b 1 * b 5 + b 0 * b 3 * b 5,
    b 3, b 1 + b 0 * b 3, b 0]

def mul (a b : Code) : Code :=
  encode (mulBits (codeBits a)
    (if codeOuter a then graphBits (codeBits b) else codeBits b))
    (Bool.xor (codeOuter a) (codeOuter b))

def inv (a : Code) : Code :=
  encode (if codeOuter a then graphBits (inverseBits (codeBits a))
    else inverseBits (codeBits a)) (codeOuter a)

def conj (g a : Code) : Code := mul (mul g a) (inv g)

theorem encode_decode : ∀ c : Code, encode (codeBits c) (codeOuter c) = c := by
  decide +kernel

theorem mul_zero : ∀ c : Code, mul c 0 = c := by decide +kernel

theorem zero_mul : ∀ c : Code, mul 0 c = c := by decide +kernel

theorem mul_inv : ∀ c : Code, mul c (inv c) = 0 := by decide +kernel

theorem inv_mul : ∀ c : Code, mul (inv c) c = 0 := by decide +kernel

end CoverageCode
end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds
