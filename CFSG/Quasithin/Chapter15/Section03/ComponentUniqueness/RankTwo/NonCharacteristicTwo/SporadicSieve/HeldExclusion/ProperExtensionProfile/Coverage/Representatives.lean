module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Candidates

/-!
# Four literal subgroups for the outer Held local calculation

The marking is the published pure pair `(false, 0)`. Its even subgroup is
normalized by the full automorphism stabilizer defined below. Four rows of
words in its four generators specify subgroups of the actual Held carrier;
their images use the actual inner-automorphism homomorphism.

The words come from the reproducible calculation in `source/discover.py`.
The definitions do not assert elementary abelianness, exhaustive coverage,
or any ambient normalizer identity. These are separate finite certificates.
In particular the rows are not the max3/max4/max5 local subgroups.

Source: Aschbacher--Smith 15.3.41--42, printed p.1138; GLS3 Table 5.3p;
the unchanged ATLAS HeG1-p2058B0 model and the published pure-pair words.
-/

@[expose] public section
open Subgroup

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CoverageData
open Held.LocalPairs Held.LocalPairs.PairCoverage.LocalActions

/-- The actual even subgroup of the first pure pair. -/
def pureTwo : Subgroup Held.He := candidateTwo false 0

/-- Its full stabilizer in the automorphism group, including outer actors. -/
def outerRepresentative : Subgroup (MulAut Held.He) := automorphismNormalizer pureTwo

/-- The four published generators, regarded as elements of their own subgroup. -/
def generator (k : Fin 4) : pureTwo :=
  ⟨evalLocalWord false (twoWord false 0 k), subset_closure (Set.mem_range_self k)⟩

/-- Signed letters are numbered one through four, in the published order. -/
def letter (k : ℤ) : pureTwo :=
  let x := generator (Fin.ofNat 4 (k.natAbs - 1))
  if k < 0 then x⁻¹ else x

/-- Word evaluation inside the literal even subgroup. -/
def word (w : List ℤ) : pureTwo := (w.map letter).prod

/-- Four proposed elementary rows, ordered by their diagnostic sizes 2,4,8,16. -/
def rowWords : Fin 4 → List (List ℤ)
  | 0 => [[-4, 2, 3, 4, 2, 3, -4, -2, -3, -4, -2, -3]]
  | 1 => [[-4, -1, 2, 3, 4, 3, 4, -2, -3, -4, -3, -1],
      [-4, 2, 3, 4, 2, 3, -4, -2, -3, -4, -2, -3]]
  | 2 => [[-4, 3, 1, 3, 4, -3, -1, -3],
      [-4, -1, -2, -4, -3, -4, -1, -2, -4, -3],
      [-4, 2, 3, 4, 2, 3, -4, -2, -3, -4, -2, -3]]
  | 3 => [[-4, -3, -4, -3], [-4, 3, 1, 3, 4, -3, -1, -3],
      [-4, -1, -2, -4, -3, -4, -1, -2, -4, -3],
      [-4, 2, 3, 4, 2, 3, -4, -2, -3, -4, -2, -3]]

/-- A row as a subgroup of the pure even subgroup. -/
def row (j : Fin 4) : Subgroup pureTwo :=
  closure {x | ∃ w ∈ rowWords j, word w = x}

/-- The same row inside Held, under its genuine inclusion. -/
def heldRow (j : Fin 4) : Subgroup Held.He := (row j).map pureTwo.subtype

/-- Its actual inner-automorphism image in the group relevant to outer coverage. -/
def ambientRow (j : Fin 4) : Subgroup (MulAut Held.He) :=
  (heldRow j).map MulAut.conj

theorem word_mem_row (j : Fin 4) (w : List ℤ) (hw : w ∈ rowWords j) :
    word w ∈ row j := subset_closure ⟨w, hw, rfl⟩

theorem heldRow_le_pureTwo (j : Fin 4) : heldRow j ≤ pureTwo := map_subtype_le _

/-- Inner conjugation by the pure subgroup preserves that subgroup. -/
theorem pureTwo_map_conj_le_outerRepresentative :
    pureTwo.map MulAut.conj ≤ outerRepresentative := by
  rintro _ ⟨x, hx, rfl⟩
  change pureTwo.map (MulAut.conj x).toMonoidHom = pureTwo
  exact mem_normalizer_iff_map_conj_eq.mp (pureTwo.le_normalizer hx)

/-- The four images lie in the same fixed full stabilizer. -/
theorem ambientRow_le_outerRepresentative (j : Fin 4) :
    ambientRow j ≤ outerRepresentative :=
  (map_mono (heldRow_le_pureTwo j)).trans pureTwo_map_conj_le_outerRepresentative

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CoverageData
