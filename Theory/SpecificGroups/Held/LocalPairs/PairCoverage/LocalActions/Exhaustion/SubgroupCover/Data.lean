module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.Contracts

/-!
# Word data for the Held local double-coset cover

The representatives and alignment words are exactly those in
`Exhaustion/source/discovery.json`. Supplemental words are produced by
`SubgroupCover/source/Generate.g`: right cosets are represented as d*b with
b in the marked two-subgroup. Every transition factor is an explicit word
in its four literal generators. None of these data assert coverage or order.

Sources: ATLAS HeG1-p2058B0 and HeG1-max3W1/max4W1; GLS3 Table 5.3p.
The carrier already inverts GAP permutations, so letter order is preserved.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover
open Subgroup

/-- Evaluate integer powers of a fixed, finite alphabet. -/
def evalPowers {G : Type*} [Group G] {n : ℕ} (g : Fin n → G)
    (w : List (Fin n × ℤ)) : G :=
  (w.map (fun t => g t.1 ^ t.2)).prod

theorem evalPowers_mem {G : Type*} [Group G] {n : ℕ} (H : Subgroup G)
    (g : Fin n → G) (hg : ∀ k, g k ∈ H) (w : List (Fin n × ℤ)) :
    evalPowers g w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons t w ih => exact H.mul_mem (H.zpow_mem (hg t.1) t.2) ih

/-- The four generators of the marked candidate, in their published order. -/
def evenGenerator (i : Bool) (k : Fin 4) : He :=
  evalLocalWord i (twoWord i 0 k)

theorem evenGenerator_mem (i : Bool) (k : Fin 4) :
    evenGenerator i k ∈ candidateTwo i 0 :=
  subset_closure ⟨k, rfl⟩

/-- The odd generators followed by the even generators, as used by GAP. -/
def productGenerator (i : Bool) (j : Fin 2) : Fin 6 → He
  | 0 => evalLocalWord i (oddWord i j 0)
  | 1 => evalLocalWord i (oddWord i j 1)
  | 2 => evalLocalWord i (twoWord i j 0)
  | 3 => evalLocalWord i (twoWord i j 1)
  | 4 => evalLocalWord i (twoWord i j 2)
  | 5 => evalLocalWord i (twoWord i j 3)

theorem productGenerator_mem (i : Bool) (j : Fin 2) (k : Fin 6) :
    productGenerator i j k ∈ candidateProduct i j := by
  match k with
  | 0 => exact mem_sup_left (subset_closure ⟨0, rfl⟩)
  | 1 => exact mem_sup_left (subset_closure ⟨1, rfl⟩)
  | 2 => exact mem_sup_right (subset_closure ⟨0, rfl⟩)
  | 3 => exact mem_sup_right (subset_closure ⟨1, rfl⟩)
  | 4 => exact mem_sup_right (subset_closure ⟨2, rfl⟩)
  | 5 => exact mem_sup_right (subset_closure ⟨3, rfl⟩)

def alignmentWord : Bool → List (Bool × ℤ)
  | false => [(false, 1), (true, 3), (false, 1), (true, 2), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1)]
  | true => [(true, -2), (false, 1), (true, -3), (false, 1), (true, -1), (false, 1), (true, -3), (false, 1), (true, 1)]

/-- GAP conjugation by c is c⁻¹ K c, hence a comap by Lean conjugation. -/
def alignment (i : Bool) : He := evalLocalWord i (alignmentWord i)

theorem alignment_mem (i : Bool) : alignment i ∈ localOvergroup i :=
  evalLocalWord_mem i _

def alignedProduct (i : Bool) (j : Fin 2) : Subgroup He :=
  if j = 0 then candidateProduct i 0
  else (candidateProduct i 1).comap (MulAut.conj (alignment i)).toMonoidHom

def representativeWord : Bool → Fin 17 → List (Bool × ℤ)
  | false, 0 => []
  | false, 1 => [(true, -1), (false, 1), (true, -1), (false, 1), (true, 2), (false, 1), (true, -2), (false, 1), (true, 1), (false, 1), (true, 1)]
  | false, 2 => [(true, -3), (false, 1), (true, -2), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1)]
  | false, 3 => [(false, 1), (true, -1), (false, 1), (true, -2), (false, 1), (true, -2), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1)]
  | false, 4 => [(true, 1), (false, 1), (true, -4), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -3)]
  | false, 5 => [(true, 1), (false, 1), (true, 3), (false, 1), (true, -2), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1)]
  | false, 6 => [(true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 2), (false, 1), (true, 3), (false, 1), (true, -2), (false, 1)]
  | false, 7 => [(true, -2), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -2)]
  | false, 8 => [(true, -1), (false, 1), (true, -1), (false, 1), (true, 3), (false, 1), (true, -2), (false, 1), (true, -1), (false, 1), (true, -2), (false, 1)]
  | false, 9 => [(true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 2), (false, 1), (true, -1), (false, 1), (true, 2), (false, 1), (true, -1)]
  | false, 10 => [(true, -4), (false, 1), (true, -3), (false, 1), (true, -2), (false, 1), (true, -2), (false, 1)]
  | false, 11 => [(false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -3), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 3), (false, 1), (true, 1), (false, 1)]
  | false, 12 => [(true, -1), (false, 1), (true, 2), (false, 1), (true, 2), (false, 1), (true, 4), (false, 1), (true, 1), (false, 1)]
  | false, 13 => [(true, 2), (false, 1), (true, 3), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1)]
  | false, 14 => [(true, 1), (false, 1), (true, -1), (false, 1), (true, -3), (false, 1), (true, 1), (false, 1), (true, 5), (false, 1)]
  | false, 15 => [(false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 3), (false, 1), (true, -3)]
  | false, _ => [(true, -3), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 3), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1)]
  | true, 0 => []
  | true, 1 => [(true, 1), (false, 1), (true, 3), (false, 1), (true, -2), (false, 1), (true, 2), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1)]
  | true, 2 => [(false, 1), (true, 4), (false, 1), (true, 1), (false, 1), (true, 2), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1)]
  | true, 3 => [(false, 1), (true, 3), (false, 1), (true, -4), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1)]
  | true, 4 => [(true, 1), (false, 1), (true, 3), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -2), (false, 1), (true, -1), (false, 1)]
  | true, 5 => [(true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 5), (false, 1), (true, 1)]
  | true, 6 => [(true, -3), (false, 1), (true, -2), (false, 1), (true, -1), (false, 1), (true, -3), (false, 1), (true, 3)]
  | true, 7 => [(true, 2), (false, 1), (true, -1), (false, 1), (true, -3), (false, 1), (true, 2), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 2)]
  | true, 8 => [(false, 1), (true, 5), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -3), (false, 1), (true, 1), (false, 1)]
  | true, 9 => [(false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 3), (false, 1)]
  | true, 10 => [(true, -1), (false, 1), (true, -1), (false, 1), (true, 2), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 2), (false, 1), (true, 2), (false, 1)]
  | true, 11 => [(false, 1), (true, -2), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -2), (false, 1), (true, -2), (false, 1)]
  | true, 12 => [(false, 1), (true, 3), (false, 1), (true, -1), (false, 1)]
  | true, 13 => [(true, -2), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -2), (false, 1), (true, 1), (false, 1), (true, 2), (false, 1), (true, 2), (false, 1), (true, 1), (false, 1)]
  | true, 14 => [(true, 1), (false, 1), (true, 2), (false, 1), (true, -2), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 3), (false, 1)]
  | true, 15 => [(false, 1), (true, 1), (false, 1), (true, -4), (false, 1), (true, -1), (false, 1), (true, -3), (false, 1), (true, 1), (false, 1), (true, -1)]
  | true, _ => [(true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -2), (false, 1), (true, -1)]

def representative (i : Bool) (r : Fin 17) : He :=
  evalLocalWord i (representativeWord i r)

theorem representative_mem (i : Bool) (r : Fin 17) :
    representative i r ∈ localOvergroup i := evalLocalWord_mem i _

/-- The four marked even generators followed by a double-coset representative. -/
def extensionGenerator (i : Bool) (r : Fin 17) : Fin 5 → He
  | 0 => evenGenerator i 0
  | 1 => evenGenerator i 1
  | 2 => evenGenerator i 2
  | 3 => evenGenerator i 3
  | 4 => representative i r

def obstructionWord : Bool → Fin 17 → List (Fin 5 × ℤ)
  | false, 0 => []
  | false, 1 => []
  | false, 2 => []
  | false, 3 => []
  | false, 4 => [(2, 1), (4, -1), (3, 1), (2, 1), (3, 1), (2, 1), (0, 1)]
  | false, 5 => [(3, 1), (2, 1), (1, 1), (4, 1), (1, 1), (2, 1), (4, -1), (3, 1), (0, 1)]
  | false, 6 => [(2, 1), (1, 1), (4, 1), (2, 1), (3, 1), (1, 1), (4, 1), (0, 1)]
  | false, 7 => [(4, -2), (2, 1), (4, -1), (2, 1), (0, 1), (4, 1)]
  | false, 8 => [(0, 1), (4, 1), (2, 1), (0, 1), (4, 1), (3, 1), (1, 1), (4, 1), (3, 1), (1, 1), (4, 1)]
  | false, 9 => []
  | false, 10 => []
  | false, 11 => [(4, 2), (0, 1), (4, 2), (2, 1), (0, 1), (4, 1), (1, 1)]
  | false, 12 => [(1, 1), (2, 1), (3, 1), (2, 1), (4, -1), (2, 1), (3, 1), (0, 1)]
  | false, 13 => [(4, -1), (3, 1), (4, -1), (1, 1), (4, -1), (2, 1), (1, 1), (2, 1), (3, 1), (2, 1)]
  | false, 14 => [(0, 1), (2, 1), (3, 1), (4, 2), (2, 1), (3, 1), (0, 1), (2, 1), (0, 1)]
  | false, 15 => [(4, 2), (1, 1), (3, 1), (0, 1), (4, -1), (1, 1)]
  | false, _ => [(1, 1), (3, 1), (0, 1), (4, 1), (1, 1), (4, 1), (2, 1), (3, 1)]
  | true, 0 => []
  | true, 1 => []
  | true, 2 => []
  | true, 3 => []
  | true, 4 => [(3, 1), (2, 1), (4, 1), (2, 1), (3, 1), (4, -1), (2, 1), (4, -1), (1, 1), (0, 1), (2, 1), (0, 1)]
  | true, 5 => [(4, 2), (1, 1), (3, 1), (2, 1), (4, 1), (2, 1), (4, -1), (2, 1)]
  | true, 6 => [(4, 3), (1, 1)]
  | true, 7 => [(2, 1), (1, 1), (0, 1), (4, 2), (1, 1), (4, 1), (2, 1), (0, 1)]
  | true, 8 => [(3, 1), (4, 2), (3, 1), (1, 1), (4, 1)]
  | true, 9 => [(4, 2), (0, 1), (4, -1)]
  | true, 10 => [(2, 1), (0, 1), (3, 1), (0, 1), (4, 2)]
  | true, 11 => [(4, 1), (1, 1), (4, -1), (1, 1)]
  | true, 12 => [(0, 1), (4, -2), (2, 1), (0, 1), (3, 1), (2, 1), (3, 1)]
  | true, 13 => []
  | true, 14 => []
  | true, 15 => [(4, 1), (1, 1), (4, 1), (1, 1)]
  | true, _ => [(1, 1), (4, 1), (3, 1), (1, 1), (2, 1), (4, -1), (2, 1)]

def obstruction (i : Bool) (r : Fin 17) : He :=
  evalPowers (extensionGenerator i r) (obstructionWord i r)

def goodIndex : Bool → Fin 17 → Option (Fin 2)
  | false, 0 => some 0
  | false, 1 => some 0
  | false, 2 => some 0
  | false, 3 => some 0
  | false, 4 => none
  | false, 5 => none
  | false, 6 => none
  | false, 7 => none
  | false, 8 => none
  | false, 9 => some 1
  | false, 10 => some 1
  | false, 11 => none
  | false, 12 => none
  | false, 13 => none
  | false, 14 => none
  | false, 15 => none
  | false, _ => none
  | true, 0 => some 0
  | true, 1 => some 0
  | true, 2 => some 0
  | true, 3 => some 0
  | true, 4 => none
  | true, 5 => none
  | true, 6 => none
  | true, 7 => none
  | true, 8 => none
  | true, 9 => none
  | true, 10 => none
  | true, 11 => none
  | true, 12 => none
  | true, 13 => some 1
  | true, 14 => some 1
  | true, 15 => none
  | true, _ => none

def membershipWord : Bool → Fin 17 → List (Fin 6 × ℤ)
  | false, 0 => []
  | false, 1 => [(0, -1), (3, 1), (0, 1)]
  | false, 2 => [(1, 1), (0, 1), (3, 1), (4, 1), (0, 1), (3, 1), (2, 1)]
  | false, 3 => [(0, -1), (1, 1), (3, 1), (4, 1), (2, 1), (1, 1), (0, 1)]
  | false, 4 => []
  | false, 5 => []
  | false, 6 => []
  | false, 7 => []
  | false, 8 => []
  | false, 9 => [(2, 1), (4, -1), (1, -1), (0, 1), (4, 1), (3, 1)]
  | false, 10 => [(4, -1), (5, 1), (1, -1), (2, 1), (4, 1), (3, 1)]
  | false, 11 => []
  | false, 12 => []
  | false, 13 => []
  | false, 14 => []
  | false, 15 => []
  | false, _ => []
  | true, 0 => []
  | true, 1 => [(1, -1), (5, 1), (0, 1), (5, 1), (4, 1), (0, 1)]
  | true, 2 => [(5, 1), (0, -1), (4, 1), (1, 1), (5, 1), (0, 1)]
  | true, 3 => [(5, 1), (0, -1), (4, 1), (5, 1), (4, 1)]
  | true, 4 => []
  | true, 5 => []
  | true, 6 => []
  | true, 7 => []
  | true, 8 => []
  | true, 9 => []
  | true, 10 => []
  | true, 11 => []
  | true, 12 => []
  | true, 13 => [(1, 1), (0, 1), (4, 1), (0, -1), (3, 1)]
  | true, 14 => [(1, 1), (4, 1), (1, 1), (5, 1), (0, -1)]
  | true, 15 => []
  | true, _ => []

def alignmentFactor : Bool → Fin 4 → List (Fin 6 × ℤ)
  | false, 0 => [(1, -1), (4, -1), (0, -1), (1, 1), (4, -1), (0, 1)]
  | false, 1 => [(1, 1), (5, 1), (1, -1), (4, 1), (2, 1), (5, 1)]
  | false, 2 => [(5, 1), (4, 1), (0, -1), (3, 1), (4, 1), (0, 1)]
  | false, 3 => [(0, -1), (5, 1), (0, 1)]
  | true, 0 => [(4, 1), (1, 1), (0, 1), (5, 1), (1, -1), (2, 1), (0, 1)]
  | true, 1 => [(4, 1), (5, 1), (1, -1), (0, -1), (5, 1), (4, 1), (1, 1), (0, 1)]
  | true, 2 => [(1, 1), (3, 1), (4, 1), (0, -1), (4, 1), (1, 1), (0, 1)]
  | true, 3 => [(4, 1), (0, 1), (5, 1), (0, 1), (4, 1), (0, 1)]

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover
