module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.RadicalOrder

/-!
# Fixed odd words for the full Hall--Janko local normalizer

These two words in the original ATLAS generators are intended to represent
the two order-three factors of the local quotient. Here only their table
values and conjugation witnesses are supplied. `QuotientSeed` proves their
membership in the full normalizer; quotient recognition and coverage are
separate obligations. Source: GLS3 Table 5.3g, ATLAS J2G1-p100B0.
Reproduce with `source/quotient-seed.py`; no GAP conclusion is a Lean premise.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.QuotientData
open Theory.GroupTheory GeneratorPair.SecondOrbitCertificate RadicalData

def oddWord (i : Fin 2) : List (Fin 3) :=
  match i.val with
  | 0 => [0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0]
  | _ => [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0]

def oddCode (i : Fin 2) : Nat :=
  match i.val with
  | 0 => 583402257071808036641995019927675794555255540393982703571258443717204372146040537642414687868115622340909254971614044232899406512498463643280939900105250859332420223256578920654910532494035892808774648891179179
  | _ => 4057197716837196081025120707768869696819712865356056800048207850556624306194305793594455300877047214873464486467999184937445244381317041106815149203699802193769593638179078281708203194046812257209806646695297152

def oddInvCode (i : Fin 2) : Nat :=
  match i.val with
  | 0 => 2355438206620414683271054843895326553257341651652962847177858343249674755873172740819933243036041692542081901292848335083988335748498501717524788836476034247359249193167939444316139200899322569162268151699521672
  | _ => 3853792957850749715774983850523769338150252687277358678043789331714583640372946559008521716844296126621874593580701197147594743966499578564519372456080894573404983919611748003898850497433902956252384512813940864

def oddMap (i : Fin 2) : Fin 100 → Fin 100 := packedMap (oddCode i)

def oddInvMap (i : Fin 2) : Fin 100 → Fin 100 := packedMap (oddInvCode i)

set_option maxRecDepth 100000 in
theorem oddTable_left : ∀ i x, oddInvMap i (oddMap i x) = x := by
  apply allFin
  decide +kernel

def oddTable (i : Fin 2) : Equiv.Perm (Fin 100) :=
  tablePerm (oddMap i) (oddInvMap i) (oddTable_left i)
    (rightInverse_of_leftInverse_fin (oddTable_left i))

def oddConjIndex (i : Fin 2) : Fin 6 → Fin 64 :=
  match i.val with
  | 0 => ![46, 30, 55, 59, 6, 26]
  | _ => ![15, 30, 52, 3, 5, 6]


end Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.QuotientData
