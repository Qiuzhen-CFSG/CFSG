module
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.FirstExclusion.FiniteModel.EnumerationData
public import Mathlib.Data.Fintype.Card

/-!
# Finite centralizer certificates for the first nonsplit Held model

The six possible noncentral squares are `targets`. Each has a 64-element
centralizer. Commuting with two specified elements restricts its center to four
rows, one of which is the identity and another the mark. The mark has 20 square
roots in that centralizer, while the remaining two rows have 12 each.

All assertions below are finite propositions proved by kernel reduction. The
bit masks only encode subsets of the certified enumeration: `centralizer_test`
checks their equality with the actual permutation centralizers. `FiniteModel`
transports these certificates to subgroups of `NonsplitModels.First`.

Source problem: Huppert--Blackburn III, XII.1.18(b), p.314, citing Held,
J. Algebra 8 (1968), 436--449, DOI 10.1016/0021-8693(68)90054-9.
-/

@[expose] public section
namespace Theory.GroupTheory.HeldM22A10.FirstExclusion.FiniteModel
open NonsplitModels
set_option maxRecDepth 10000
def centralizerMask : Fin 6 → ℕ := ![769613038218004273107281142933846034592983375653092273142625935279875886944207706292467009689574103245772345065489, 1539460565846022545949623749025181879606257917441602545909210577061542480496632126215749903826893421593800158494753, 769613038218004273107281142933846034592983375653092273142625935279875886944207706292467009689574103245772345065489, 1539460565846022545949623749025181879606257917441602545909210577061542480496632126215749903826893421593800158494753, 32034798108350596261901267629262543522278726660094186929381254407243331109009037557835950103270524574609566044012553, 32034798108350596261901267629262543522278726660094186929381254407243331109009037557835950103270524574609566044012553]

def centerIndices : Fin 6 → Fin 4 → Index := ![![0, 19, 195, 357], ![0, 24, 210, 357], ![0, 19, 195, 357], ![0, 24, 210, 357], ![0, 213, 236, 357], ![0, 213, 236, 357]]

def centerWitnesses : Fin 6 → Fin 2 → Index := ![![24, 46], ![19, 52], ![24, 46], ![19, 52], ![3, 19], ![3, 19]]

def inCentralizer (k : Fin 6) (i : Index) : Prop := (centralizerMask k).testBit i.val = true
instance (k : Fin 6) (i : Index) : Decidable (inCentralizer k i) := inferInstanceAs (Decidable (_ = _))

def rootCount (k : Fin 6) (z : Index) : ℕ :=
  Fintype.card {i : Index // inCentralizer k i ∧ square i = z}

set_option maxHeartbeats 800000 in
theorem center_test : ∀ i : Index,
    perm i * firstA = firstA * perm i → perm i * firstB = firstB * perm i →
    i = 0 ∨ i = markIndex := by decide +kernel

set_option maxHeartbeats 800000 in
theorem involution_test : ∀ i : Index, square i = 0 → (action i 0).val % 2 = 0 := by
  decide +kernel

set_option maxHeartbeats 800000 in
theorem square_test : ∀ i : Index, (action i 0).val % 2 = 0 → square i ≠ 0 →
    square (square i) = 0 → square i ≠ markIndex → ∃ k, square i = targets k := by
  decide +kernel

set_option maxHeartbeats 800000 in
theorem centralizer_test : ∀ k i, inCentralizer k i ↔
    perm (targets k) * perm i = perm i * perm (targets k) := by decide +kernel

set_option maxHeartbeats 800000 in
theorem centralizer_card_test : ∀ k, Fintype.card {i : Index // inCentralizer k i} = 64 := by
  decide +kernel

set_option maxHeartbeats 800000 in
theorem witness_mem_test : ∀ k j, inCentralizer k (centerWitnesses k j) := by decide +kernel

set_option maxHeartbeats 800000 in
theorem center_restriction_test : ∀ k i, inCentralizer k i →
    perm (centerWitnesses k 0) * perm i = perm i * perm (centerWitnesses k 0) →
    perm (centerWitnesses k 1) * perm i = perm i * perm (centerWitnesses k 1) →
    i = 0 ∨ i = markIndex ∨ i = centerIndices k 1 ∨ i = centerIndices k 2 := by
  decide +kernel

set_option maxHeartbeats 800000 in
theorem mark_count_test : ∀ k, rootCount k markIndex = 20 := by decide +kernel

set_option maxHeartbeats 800000 in
theorem other_count_test : ∀ k, rootCount k (centerIndices k 1) = 12 ∧
    rootCount k (centerIndices k 2) = 12 := by decide +kernel

end Theory.GroupTheory.HeldM22A10.FirstExclusion.FiniteModel
