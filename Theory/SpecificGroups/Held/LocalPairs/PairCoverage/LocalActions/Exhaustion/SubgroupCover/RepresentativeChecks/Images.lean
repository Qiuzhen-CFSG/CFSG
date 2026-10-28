module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover.Data
public import Mathlib.Tactic.FinCases
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.ResidualRoots.Pair00.Alphabet
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.ResidualRoots.Pair01.Alphabet
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.ResidualRoots.Pair10.Alphabet
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.ResidualRoots.Pair11.Alphabet

/-!
# Certified permutation images for the Held cover checks

The six product generators are exactly the previously certified residual-pair
alphabet. Reuse those packed permutations, and the checked local generators,
to evaluate the literal cover words without expanding their nested definitions.
Every comparison with the actual Held representation is proved here; the
lookup tables introduce no new group or recognition premise.

Sources: ATLAS HeG1-p2058B0 and max3W1/max4W1, GLS3 Table 5.3p;
SubgroupCover/source/factors.json and Exhaustion/source/discovery.json.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover.RepresentativeChecks
open RepresentativeImages
set_option maxRecDepth 8192

def fastLocal (i : Bool) : Equiv.Perm (Fin 2058) :=
  if i then Local1.localPerm else Local0.localPerm

theorem fastLocal_eq (i : Bool) : fastLocal i = representation (localWord i) := by
  cases i
  · exact Local0.localPerm_eq
  · exact Local1.localPerm_eq

def fastProduct : Bool → Fin 2 → Fin 6 → Equiv.Perm (Fin 2058)
  | false, 0, 0 => Pair00.odd0
  | false, 0, 1 => Pair00.odd1
  | false, 0, 2 => Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair2
  | false, 0, 3 => Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair3
  | false, 0, 4 => Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair4
  | false, 0, 5 => Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair5
  | false, 1, 0 => Pair01.odd0
  | false, 1, 1 => Pair01.odd1
  | false, 1, 2 => Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair01.pair2
  | false, 1, 3 => Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair01.pair3
  | false, 1, 4 => Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair01.pair4
  | false, 1, 5 => Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair01.pair5
  | true, 0, 0 => Pair10.odd0
  | true, 0, 1 => Pair10.odd1
  | true, 0, 2 => Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair10.pair2
  | true, 0, 3 => Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair10.pair3
  | true, 0, 4 => Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair10.pair4
  | true, 0, 5 => Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair10.pair5
  | true, 1, 0 => Pair11.odd0
  | true, 1, 1 => Pair11.odd1
  | true, 1, 2 => Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair11.pair2
  | true, 1, 3 => Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair11.pair3
  | true, 1, 4 => Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair11.pair4
  | true, 1, 5 => Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair11.pair5

theorem fastProduct_eq (i : Bool) (j : Fin 2) (k : Fin 6) :
    fastProduct i j k = representation (productGenerator i j k) := by
  cases i <;> fin_cases j <;> fin_cases k
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair0_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair1_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair2_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair3_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair4_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair00.pair5_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair01.pair0_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair01.pair1_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair01.pair2_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair01.pair3_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair01.pair4_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair01.pair5_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair10.pair0_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair10.pair1_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair10.pair2_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair10.pair3_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair10.pair4_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair10.pair5_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair11.pair0_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair11.pair1_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair11.pair2_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair11.pair3_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair11.pair4_eq
  · exact Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots.Pair11.pair5_eq

def fastEven (i : Bool) : Fin 4 → Equiv.Perm (Fin 2058)
  | 0 => fastProduct i 0 2
  | 1 => fastProduct i 0 3
  | 2 => fastProduct i 0 4
  | 3 => fastProduct i 0 5

theorem fastEven_eq (i : Bool) (k : Fin 4) :
    fastEven i k = representation (evenGenerator i k) := by
  fin_cases k
  · exact fastProduct_eq i 0 2
  · exact fastProduct_eq i 0 3
  · exact fastProduct_eq i 0 4
  · exact fastProduct_eq i 0 5

theorem rep_powers {n : ℕ} (g : Fin n → He) (w : List (Fin n × ℤ)) :
    representation (evalPowers g w) = evalPowers (fun k => representation (g k)) w := by
  induction w with
  | nil => exact map_one representation
  | cons t w ih =>
    change representation (g t.1 ^ t.2 * evalPowers g w) = _
    rw [map_mul, map_zpow, ih]
    rfl

def fastWord (i : Bool) (w : List (Bool × ℤ)) : Equiv.Perm (Fin 2058) :=
  (w.map (fun t => (if t.1 then fastLocal i else TwoLocalCandidates.Cores.Tables0.p0) ^ t.2)).prod

theorem packedA_eq : TwoLocalCandidates.Cores.Tables0.p0 = atlasA :=
  TwoLocalCandidates.Cores.Tables0.p0_eq

theorem rep_local (i : Bool) (w : List (Bool × ℤ)) :
    representation (evalLocalWord i w) = fastWord i w := by
  rw [representation_evalLocalWord]
  simp only [fastWord, fastLocal_eq, packedA_eq]

def fastExtension (i : Bool) (r : Fin 17) : Fin 5 → Equiv.Perm (Fin 2058)
  | 0 => fastEven i 0
  | 1 => fastEven i 1
  | 2 => fastEven i 2
  | 3 => fastEven i 3
  | 4 => fastWord i (representativeWord i r)

theorem fastExtension_eq (i : Bool) (r : Fin 17) (k : Fin 5) :
    fastExtension i r k = representation (extensionGenerator i r k) := by
  fin_cases k
  · exact fastEven_eq i 0
  · exact fastEven_eq i 1
  · exact fastEven_eq i 2
  · exact fastEven_eq i 3
  · exact (rep_local i _).symm

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover.RepresentativeChecks
