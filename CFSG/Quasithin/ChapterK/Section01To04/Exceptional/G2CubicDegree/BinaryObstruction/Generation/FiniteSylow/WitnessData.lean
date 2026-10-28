module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Generation.FiniteSylow.Coverage
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Generation.FiniteSylow.Certificate

/-!
# Actual derived conjugators for the eight binary Sylow actors

The chosen elements and three generators belong to the literal subgroups from
`Coverage`. Conjugating words use C E F, F S, and E R; their membership in the
actual commutator subgroup follows from the checked binary parabolic APIs.
The matrix certificate modules prove generation using these exact elements.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.3,
manuscript pp.10--11. Root conventions are inherited from the ATLAS port;
Gerald Höhn and the ATLAS contributors, ATLAS Research and Attribution License
1.0 (LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff).
-/

@[expose] public section

open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion
open Atlas.G2.BinaryCore Atlas.G2.BinaryParabolicPair Atlas.G2.BinaryParabolicPair.SevenSylowOvergroups
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.FiniteSylow
open Certificate

def basisIndex (i : Fin 8) : Fin 3 → Fin 8 :=
  ![![2,4,5], ![4,6,7], ![4,7,6], ![4,6,3],
    ![4,7,6], ![6,2,5], ![2,7,6], ![2,6,7]] i

def chosenIndex (i : Fin 8) : Fin 8 := ![3,6,3,5,5,7,2,6] i

def basisElement (i : Fin 8) (j : Fin 3) : G := element (row i (basisIndex i j))
def chosen (i : Fin 8) : G := element (row i (chosenIndex i))

def derivedLetter : Fin 3 → G := ![sylowGenerator, cubicActor, movingActor]

theorem derivedLetter_mem (i : Fin 3) : derivedLetter i ∈ commutator G := by
  fin_cases i
  · exact sylowGenerator_mem.2
  · exact cubicActor_mem_derived
  · exact movingActor_mem_derived

def conjugatorWord : Fin 8 → List (Fin 3) :=
  ![[2,1,2,1], [1,2,1,2,1], [2,1,2], [1,2,1],
    [2,1,2], [1,2,1], [2,1,2,1], [1,2,1,2]]

def conjugator (i : Fin 8) : Derived :=
  ⟨word derivedLetter (conjugatorWord i), word_mem _ _ derivedLetter_mem _⟩

def supplement (i : Fin 8) : G := (conjugator i).val * chosen i * (conjugator i).val⁻¹

def recoveryLetter (i : Fin 8) : Fin 4 → G :=
  ![basisElement i 0, basisElement i 1, basisElement i 2, supplement i]

theorem chosen_mem (i : Fin 8) : chosen i ∈ candidate i := ⟨chosenIndex i,rfl⟩

theorem recoveryLetter_mem (i : Fin 8) (j : Fin 4) :
    recoveryLetter i j ∈ candidate i ⊔ Subgroup.zpowers (supplement i) := by
  fin_cases j
  · exact Subgroup.mem_sup_left ⟨basisIndex i 0,rfl⟩
  · exact Subgroup.mem_sup_left ⟨basisIndex i 1,rfl⟩
  · exact Subgroup.mem_sup_left ⟨basisIndex i 2,rfl⟩
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.FiniteSylow
