module

public import Theory.SpecificGroups.Tits.ConverseLocalCoverage.Representatives
public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.Packed
public import Theory.SpecificGroups.Tits.R1Certificate.Data
public import Mathlib.Data.List.Forall2

/-!
# Executable double-coset factorization checks

The Sylow normal forms use the mixed radices 2,2,4,2,4,2,4,2.
A 27-bit witness records two normal forms and one of the eighteen published
positive words. Five witnesses form a row, indexed by the first-parabolic
rotation exponent. The checker compares the permutations at 0, 1, 2; the
order certificate proves that these points form a base in `Base`.

Source: Parrott (1972), section 5, p.683, and the existing Atlas point tables.
-/

@[expose] public section
namespace Tits.ConverseLocalCoverage.DoubleCosetCertificate
open Theory.GroupTheory.CosetEnumeration OuterOddSubgroups.OverlapCentralizers

def code : ParrottGenerator → Fin 10
  | .r1 => 0 | .r8 => 1 | .s1 => 2 | .s2 => 3 | .s3 => 4
  | .s4 => 5 | .s5 => 6 | .s6 => 7 | .s7 => 8 | .s8 => 9

def fastEval (w : Word ParrottGenerator) : Equiv.Perm (Fin 1600) :=
  (w.map fun a => if a.2 then Packed.perm (code a.1) else Packed.perm (code a.1) ^ 3).prod

def fastNormalForm (n : Fin 2048) : Equiv.Perm (Fin 1600) :=
  Packed.perm 2 ^ (n.val % 2) *
    Packed.perm 3 ^ (n.val / 2 % 2) *
    Packed.perm 4 ^ (n.val / 4 % 4) *
    Packed.perm 5 ^ (n.val / 16 % 2) *
    Packed.perm 6 ^ (n.val / 32 % 4) *
    Packed.perm 7 ^ (n.val / 128 % 2) *
    Packed.perm 8 ^ (n.val / 256 % 4) *
    Packed.perm 9 ^ (n.val / 1024 % 2)

def fastRep (k : Fin 18) : Equiv.Perm (Fin 1600) :=
  ((doubleCosetWord k).map fun a => Packed.perm (code a)).prod

def witnessLeft (c : Nat) : Fin 2048 := ⟨c % 2048, Nat.mod_lt _ (by decide)⟩
def witnessRight (c : Nat) : Fin 2048 := ⟨c / 2048 % 2048, Nat.mod_lt _ (by decide)⟩
def witnessRep (c : Nat) : Fin 18 := ⟨c / 4194304 % 18, Nat.mod_lt _ (by decide)⟩
def rowWitness (row : Nat) (j : Fin 5) : Nat := (row >>> (27 * j.val)) % 134217728

def test (w : Word ParrottGenerator) (j : Fin 5) (c : Nat) : Bool :=
  let g := (Packed.perm 2 * Packed.perm 0) ^ j.val * fastEval w
  let h := fastNormalForm (witnessLeft c) * fastRep (witnessRep c) *
    fastNormalForm (witnessRight c)
  g 0 == h 0 && g 1 == h 1 && g 2 == h 2

def testRow (w : Word ParrottGenerator) (row : Nat) : Bool :=
  (List.finRange 5).all (fun j => test w j (rowWitness row j))

end Tits.ConverseLocalCoverage.DoubleCosetCertificate
