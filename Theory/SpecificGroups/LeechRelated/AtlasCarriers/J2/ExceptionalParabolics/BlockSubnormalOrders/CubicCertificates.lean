module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.CandidateQuotient.Checks

/-!
# Small certificates for the cubic action on the Hall--Janko radical

The first nine retained quotient representatives form a group of order nine.
Their multiplication indices and vanishing radical factors are checked here;
the actual permutation multiplication is reused from `CandidateQuotient.Checks`.
For each nonidentity representative, thirteen selected radical words yield
commutators distinguished by their images at points zero and one. Every check
uses kernel reduction on the unchanged degree-100 ATLAS permutations.

The selections can be reproduced by `source/check_witnesses.py`. The original
ATLAS attribution is retained in `PairNormalizer/source`. This is the concrete
local calculation used for Aschbacher--Smith 2.3.9(7), printed p.526; the source
local group is GLS3 Table 5.3g. The original code here is Apache 2.0.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.BlockSubnormalOrders
open PairNormalizer PairNormalizer.CandidateQuotient PairNormalizer.RadicalData
open GeneratorPair.SecondOrbitCertificate
open scoped commutatorElement

def cubicInput (r : Fin 9) : Fin 13 → Fin 64 :=
  match r.val with
  | 1 | 2 => ![0, 1, 2, 3, 4, 7, 8, 9, 12, 13, 18, 27, 32]
  | 3 | 6 => ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  | 4 | 8 => ![0, 1, 2, 4, 5, 37, 6, 10, 42, 11, 14, 46, 24]
  | _ => ![0, 3, 4, 5, 6, 18, 42, 19, 20, 52, 53, 23, 24]

def cubicCommKey (r : Fin 9) (i : Fin 13) : Fin 100 × Fin 100 :=
  let c := ⁅qTable (cubicInput r i), repTable (r.castLE (by decide))⁆
  (c 0, c 1)

set_option maxRecDepth 100000 in
theorem cubicCommKey_injective : ∀ r : Fin 9, r ≠ 0 → Function.Injective (cubicCommKey r) := by
  apply allFin
  decide +kernel

def nineMul (i j : Fin 9) : Fin 9 :=
  ⟨((i.val / 3 + j.val / 3) % 3) * 3 + (i.val % 3 + j.val % 3) % 3, by omega⟩

def nineInv : Fin 9 → Fin 9 := ![0, 2, 1, 6, 8, 7, 3, 5, 4]

theorem nineMul_inv : ∀ i, nineMul i (nineInv i) = 0 := by decide +kernel

theorem nine_mulIndex : ∀ i j : Fin 9,
    mulIndex (i.castLE (by decide)) (j.castLE (by decide)) =
      (nineMul i j).castLE (by decide) := by decide +kernel

theorem nine_radicalFactor : ∀ i j : Fin 9,
    radicalFactor (i.castLE (by decide)) (j.castLE (by decide)) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem nine_key_injective : Function.Injective (fun i : Fin 9 =>
    (repTable (i.castLE (by decide)) 0, repTable (i.castLE (by decide)) 1,
      repTable (i.castLE (by decide)) 2)) := by decide +kernel
end Sporadic.LeechRelated.J2.ExceptionalParabolics.BlockSubnormalOrders
