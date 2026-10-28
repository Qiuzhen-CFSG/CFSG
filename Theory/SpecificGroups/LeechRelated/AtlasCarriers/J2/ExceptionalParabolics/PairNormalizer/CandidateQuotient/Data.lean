module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.QuotientSeed

/-!
# Multiplication witnesses for the candidate quotient

The eighteen words are t^b u^i v^j, for b < 2 and i,j < 3, in the
three fixed normalizer generators. The model uses the transposition (0 1),
the cycle (0 1 2), and the generator of Multiplicative (ZMod 3).
For each product the table gives its model index and a left radical factor.
The checks in `Checks` verify all witnesses against the degree-100 carrier.

Source: GLS3 Table 5.3g; Aschbacher--Smith, printed p.511 (PDF p.528).
Generated from the unchanged Seed and the ATLAS words in
`PairNormalizer/source/quotient-seed.json`. Python supplies witnesses only.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.CandidateQuotient
open Theory.GroupTheory GeneratorPair.SecondOrbitCertificate Seed

def repWord (i : Fin 18) : List (Fin 3) :=
  match i.val with
  | 0 => []
  | 1 => [2]
  | 2 => [2, 2]
  | 3 => [1]
  | 4 => [1, 2]
  | 5 => [1, 2, 2]
  | 6 => [1, 1]
  | 7 => [1, 1, 2]
  | 8 => [1, 1, 2, 2]
  | 9 => [0]
  | 10 => [0, 2]
  | 11 => [0, 2, 2]
  | 12 => [0, 1]
  | 13 => [0, 1, 2]
  | 14 => [0, 1, 2, 2]
  | 15 => [0, 1, 1]
  | 16 => [0, 1, 1, 2]
  | _ => [0, 1, 1, 2, 2]

def mulIndex (i : Fin 18) : Fin 18 → Fin 18 :=
  match i.val with
  | 0 => ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
  | 1 => ![1, 2, 0, 4, 5, 3, 7, 8, 6, 10, 11, 9, 13, 14, 12, 16, 17, 15]
  | 2 => ![2, 0, 1, 5, 3, 4, 8, 6, 7, 11, 9, 10, 14, 12, 13, 17, 15, 16]
  | 3 => ![3, 4, 5, 6, 7, 8, 0, 1, 2, 15, 16, 17, 9, 10, 11, 12, 13, 14]
  | 4 => ![4, 5, 3, 7, 8, 6, 1, 2, 0, 16, 17, 15, 10, 11, 9, 13, 14, 12]
  | 5 => ![5, 3, 4, 8, 6, 7, 2, 0, 1, 17, 15, 16, 11, 9, 10, 14, 12, 13]
  | 6 => ![6, 7, 8, 0, 1, 2, 3, 4, 5, 12, 13, 14, 15, 16, 17, 9, 10, 11]
  | 7 => ![7, 8, 6, 1, 2, 0, 4, 5, 3, 13, 14, 12, 16, 17, 15, 10, 11, 9]
  | 8 => ![8, 6, 7, 2, 0, 1, 5, 3, 4, 14, 12, 13, 17, 15, 16, 11, 9, 10]
  | 9 => ![9, 10, 11, 12, 13, 14, 15, 16, 17, 0, 1, 2, 3, 4, 5, 6, 7, 8]
  | 10 => ![10, 11, 9, 13, 14, 12, 16, 17, 15, 1, 2, 0, 4, 5, 3, 7, 8, 6]
  | 11 => ![11, 9, 10, 14, 12, 13, 17, 15, 16, 2, 0, 1, 5, 3, 4, 8, 6, 7]
  | 12 => ![12, 13, 14, 15, 16, 17, 9, 10, 11, 6, 7, 8, 0, 1, 2, 3, 4, 5]
  | 13 => ![13, 14, 12, 16, 17, 15, 10, 11, 9, 7, 8, 6, 1, 2, 0, 4, 5, 3]
  | 14 => ![14, 12, 13, 17, 15, 16, 11, 9, 10, 8, 6, 7, 2, 0, 1, 5, 3, 4]
  | 15 => ![15, 16, 17, 9, 10, 11, 12, 13, 14, 3, 4, 5, 6, 7, 8, 0, 1, 2]
  | 16 => ![16, 17, 15, 10, 11, 9, 13, 14, 12, 4, 5, 3, 7, 8, 6, 1, 2, 0]
  | _ => ![17, 15, 16, 11, 9, 10, 14, 12, 13, 5, 3, 4, 8, 6, 7, 2, 0, 1]

def radicalFactor (i : Fin 18) : Fin 18 → Fin 64 :=
  match i.val with
  | 0 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 1 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 19, 19, 19, 19, 19, 19, 19, 19]
  | 2 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 42, 42, 42, 42, 42, 42, 42, 42]
  | 3 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 44, 44, 44, 44, 44, 44, 44, 44, 44]
  | 4 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60]
  | 5 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8]
  | 6 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 50]
  | 7 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28]
  | 8 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10]
  | 9 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | 10 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 53, 53, 53, 53, 53, 53, 53, 53, 53]
  | 11 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24]
  | 12 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 12, 12, 12, 12, 12, 12, 12, 12]
  | 13 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28, 28]
  | 14 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10]
  | 15 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 13, 13, 13, 13, 13, 13, 13, 13]
  | 16 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 60, 60, 60, 60, 60, 60, 60, 60, 60]
  | _ => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 8, 8, 8, 8, 8, 8, 8, 8]

def modelGenerator : Fin 3 → QuotientModel :=
  ![(Equiv.swap 0 1, 1),
    (Equiv.swap 0 1 * Equiv.swap 1 2, 1),
    (1, Multiplicative.ofAdd (1 : ZMod 3))]

def model (i : Fin 18) : QuotientModel := evalWord modelGenerator (repWord i)

def repTable (i : Fin 18) : Equiv.Perm (Fin 100) :=
  evalWord ![SylowData.tTable, QuotientData.oddTable 0, QuotientData.oddTable 1] (repWord i)

end Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.CandidateQuotient
