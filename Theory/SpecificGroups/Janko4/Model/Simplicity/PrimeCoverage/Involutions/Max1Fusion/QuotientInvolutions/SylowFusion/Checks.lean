module
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.SylowFusion.Data
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.SylowFusion.Conjugators
import Mathlib.Tactic.FinCases
/-!
# Kernel-checked involution fusion throughout the word table

For each word-table entry we certify one of three facts: it is the identity,
its square is not the identity, or an explicit conjugator sends it to a marked
target. Each conjugator is a checked ambient conjugator followed by a word in
the fixed candidate generators, hence belongs to `StarGroup` by construction.

The local conjugation words were discovered by breadth-first conjugation from
the representatives in `../source/fusion.json`. Every resulting equation is
checked here. Neither the reported class sizes nor their exhaustiveness is
used: `Coverage` supplies exhaustiveness independently.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
@[expose] public section
namespace Janko4.Simplicity.Max1Fusion.QuotientInvolutions.SylowFusionCertificate
open Cardinality.QuotientCount.Image Theory.GroupTheory

def classIndex0 : Fin 32 → Fin 25 :=
  ![0, 13, 12, 18, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 18, 0, 0, 21, 0, 0, 13, 0, 0, 0, 0, 0]

def localWord0 : Fin 32 → List (Fin 4) :=
  ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0], [], [], [0], [], [], [0], [], [], [1], [], [], [], [], []]

def classIndex1 : Fin 32 → Fin 25 :=
  ![21, 0, 13, 0, 12, 0, 0, 0, 21, 0, 0, 13, 0, 0, 12, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0]

def localWord1 : Fin 32 → List (Fin 4) :=
  ![[1], [], [2], [], [2], [], [], [], [2], [], [], [3], [], [], [3], [], [], [3], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def classIndex2 : Fin 32 → Fin 25 :=
  ![22, 0, 0, 1, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 6, 0, 0, 0, 22]

def localWord2 : Fin 32 → List (Fin 4) :=
  ![[2], [], [], [], [], [], [0, 3], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0], [], [], [], [], [], [], []]

def classIndex3 : Fin 32 → Fin 25 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def localWord3 : Fin 32 → List (Fin 4) :=
  ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def classIndex4 : Fin 32 → Fin 25 :=
  ![0, 19, 21, 19, 0, 0, 21, 0, 12, 0, 0, 0, 0, 21, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def localWord4 : Fin 32 → List (Fin 4) :=
  ![[], [], [1, 2, 3, 2, 1], [0], [], [], [1, 2, 3, 2], [], [0, 2], [], [], [], [], [2, 1, 3, 2], [], [], [0, 1], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def classIndex5 : Fin 32 → Fin 25 :=
  ![17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 17, 21, 0, 0, 0, 20, 0, 17, 0, 20, 18, 0, 0, 0, 13, 0, 0, 0, 0, 0]

def localWord5 : Fin 32 → List (Fin 4) :=
  ![[0], [], [], [], [], [], [], [], [], [], [], [3], [], [1, 2, 3, 1, 2], [], [], [], [3], [], [0, 3], [], [1, 3], [0, 3], [], [], [], [1, 2], [], [], [], [], []]

def classIndex6 : Fin 32 → Fin 25 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0]

def localWord6 : Fin 32 → List (Fin 4) :=
  ![[], [], [], [], [], [], [], [], [], [], [], [], [1], [], [], [], [2, 1], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def classIndex7 : Fin 32 → Fin 25 :=
  ![0, 18, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 12, 0, 0]

def localWord7 : Fin 32 → List (Fin 4) :=
  ![[], [3, 1], [], [], [], [0, 2], [], [], [], [], [], [], [], [], [], [], [1, 2], [], [], [], [], [], [], [3, 2], [], [], [], [], [], [3, 2], [], []]

def classIndex8 : Fin 32 → Fin 25 :=
  ![0, 0, 12, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0]

def localWord8 : Fin 32 → List (Fin 4) :=
  ![[], [], [0, 3], [], [], [], [], [], [], [1, 3], [], [], [], [], [], [], [], [], [], [], [], [2, 3], [], [], [], [], [], [], [], [], [3, 1, 3], []]

def classIndex9 : Fin 32 → Fin 25 :=
  ![0, 0, 0, 0, 15, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 0, 0, 7, 0, 0, 0, 0, 0, 7, 0, 0]

def localWord9 : Fin 32 → List (Fin 4) :=
  ![[], [], [], [], [], [], [0], [], [], [], [], [], [], [], [], [], [], [], [], [], [2, 1], [], [], [], [], [], [], [], [], [0], [], []]

def classIndex10 : Fin 32 → Fin 25 :=
  ![0, 0, 23, 0, 0, 0, 22, 0, 0, 22, 0, 0, 0, 0, 9, 0, 23, 0, 0, 0, 23, 0, 0, 0, 0, 0, 9, 4, 0, 0, 0, 0]

def localWord10 : Fin 32 → List (Fin 4) :=
  ![[], [], [0, 1], [], [], [], [0], [], [], [0, 2], [], [], [], [], [], [], [1], [], [], [], [1, 2], [], [], [], [], [], [0], [3], [], [], [], []]

def classIndex11 : Fin 32 → Fin 25 :=
  ![0, 0, 0, 8, 0, 0, 15, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0]

def localWord11 : Fin 32 → List (Fin 4) :=
  ![[], [], [], [0], [], [], [3], [], [], [], [], [], [], [1], [], [], [], [], [], [], [], [], [], [], [], [0, 3], [], [], [], [], [], []]

def classIndex12 : Fin 32 → Fin 25 :=
  ![23, 0, 23, 0, 0, 0, 0, 0, 0, 0, 22, 0, 0, 0, 0, 0, 0, 0, 22, 0, 0, 0, 0, 22, 0, 22, 0, 0, 0, 0, 0, 16]

def localWord12 : Fin 32 → List (Fin 4) :=
  ![[2], [], [], [], [], [], [], [], [], [], [2, 1], [], [], [], [], [], [], [], [0, 1], [], [], [], [], [1], [], [1, 2], [], [], [], [], [], [0]]

def classIndex13 : Fin 32 → Fin 25 :=
  ![0, 11, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0]

def localWord13 : Fin 32 → List (Fin 4) :=
  ![[], [2], [], [], [], [1], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0], [], [], [1], [], [], [], [], [], [], [], []]

def classIndex14 : Fin 32 → Fin 25 :=
  ![15, 0, 0, 0, 0, 0, 6, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def localWord14 : Fin 32 → List (Fin 4) :=
  ![[0, 3, 2], [], [], [], [], [], [2], [0, 2], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def classIndex15 : Fin 32 → Fin 25 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def localWord15 : Fin 32 → List (Fin 4) :=
  ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def classIndex16 : Fin 32 → Fin 25 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 21, 19, 0, 0, 0, 0, 0, 20, 0, 0, 21, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 19, 0, 0]

def localWord16 : Fin 32 → List (Fin 4) :=
  ![[], [], [], [], [], [], [], [], [2, 1, 3, 1], [3], [], [], [], [], [], [0], [], [], [2, 1, 3], [], [], [], [0, 1], [], [], [], [], [], [], [3, 1], [], []]

def classIndex17 : Fin 32 → Fin 25 :=
  ![0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 20, 0, 0, 0, 17, 14, 20, 0, 19, 18, 0]

def localWord17 : Fin 32 → List (Fin 4) :=
  ![[], [1, 2, 3], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0, 1, 3, 1], [], [], [], [1, 3, 2], [], [], [], [1, 3, 1], [3, 2], [0, 3, 1], [], [0, 3, 1], [0, 3, 1], []]

def classIndex18 : Fin 32 → Fin 25 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 14, 0, 0, 12, 0, 0, 17, 0, 12, 0, 0, 12, 0, 0, 0, 0, 0, 0]

def localWord18 : Fin 32 → List (Fin 4) :=
  ![[], [], [], [], [], [], [], [], [], [], [2], [], [], [], [], [], [], [2, 3, 2], [], [], [1], [], [0, 2, 3, 2], [], [], [0, 3, 2], [], [], [], [], [], []]

def classIndex19 : Fin 32 → Fin 25 :=
  ![0, 0, 20, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 17, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 0]

def localWord19 : Fin 32 → List (Fin 4) :=
  ![[], [], [0, 1, 3], [], [0, 3], [], [], [], [], [], [], [], [], [], [0, 1, 3], [0, 1], [1, 3], [], [], [], [], [], [], [], [], [], [], [], [], [], [2, 0], []]

def classIndex20 : Fin 32 → Fin 25 :=
  ![0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 17, 20, 0, 0, 17, 20]

def localWord20 : Fin 32 → List (Fin 4) :=
  ![[], [], [], [], [3, 1, 2], [], [], [], [], [], [], [0, 3], [], [], [], [], [], [], [1, 2, 3, 1], [], [], [], [], [], [], [], [3, 1], [3, 1], [], [], [0, 3, 1], [3, 2]]

def classIndex21 : Fin 32 → Fin 25 :=
  ![0, 0, 0, 14, 0, 14, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0]

def localWord21 : Fin 32 → List (Fin 4) :=
  ![[], [], [], [2, 0, 2], [], [3, 1], [], [3], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0, 2, 3], [], [], []]

def classIndex22 : Fin 32 → Fin 25 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def localWord22 : Fin 32 → List (Fin 4) :=
  ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [1, 3, 2], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def classIndex23 : Fin 32 → Fin 25 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0]

def localWord23 : Fin 32 → List (Fin 4) :=
  ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [3, 1, 3], [], [], [], [], [], []]

def classIndex24 : Fin 32 → Fin 25 :=
  ![0, 0, 0, 0, 0, 12, 8, 23, 23, 0, 10, 0, 16, 11, 0, 8, 0, 0, 0, 0, 0, 0, 11, 10, 0, 6, 11, 7, 10, 7, 24, 0]

def localWord24 : Fin 32 → List (Fin 4) :=
  ![[], [], [], [], [], [3, 2, 3], [1, 3, 1], [0], [0, 2], [], [], [], [], [1, 3], [], [1, 3], [], [], [], [], [], [], [3], [1], [], [0, 2], [1], [2], [0, 1], [0, 2], [1, 3], []]

def classIndex25 : Fin 32 → Fin 25 :=
  ![8, 8, 24, 0, 0, 0, 11, 0, 0, 0, 0, 11, 0, 24, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 9, 0, 24, 16, 0, 16, 15, 0]

def localWord25 : Fin 32 → List (Fin 4) :=
  ![[0, 1, 3], [0, 1], [0, 2], [], [], [], [0, 3], [], [], [], [], [], [], [0, 2, 1], [], [], [], [], [3], [], [], [], [], [], [0, 1], [], [0], [0, 3, 2], [], [3, 2], [3, 2], []]

def classIndex26 : Fin 32 → Fin 25 :=
  ![0, 0, 0, 0, 0, 0, 10, 4, 0, 0, 0, 24, 0, 24, 24, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def localWord26 : Fin 32 → List (Fin 4) :=
  ![[], [], [], [], [], [], [0], [3, 1], [], [], [], [1], [], [], [1, 2], [], [], [], [0, 1, 3, 1], [], [], [], [], [], [], [], [], [], [], [], [], []]

def classIndex27 : Fin 32 → Fin 25 :=
  ![0, 0, 0, 0, 0, 0, 0, 24, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 16, 0, 0, 0, 0]

def localWord27 : Fin 32 → List (Fin 4) :=
  ![[], [], [], [], [], [], [], [0, 1], [0, 2, 0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0, 1, 3], [0, 3, 2, 3], [], [], [], []]

def classIndex28 : Fin 32 → Fin 25 :=
  ![0, 0, 0, 24, 0, 0, 0, 0, 24, 24, 24, 0, 24, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 5, 0, 0]

def localWord28 : Fin 32 → List (Fin 4) :=
  ![[], [], [], [0, 3], [], [], [], [], [2, 0], [2], [2, 1], [], [3], [], [0, 1, 2], [], [], [], [], [], [], [], [], [], [], [], [0, 3], [], [], [0], [], []]

def classIndex29 : Fin 32 → Fin 25 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def localWord29 : Fin 32 → List (Fin 4) :=
  ![[], [], [], [], [], [], [], [], [], [], [], [0, 3, 2, 3], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def classIndex30 : Fin 32 → Fin 25 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 17, 0, 0, 0, 17, 18, 0, 17, 17, 12]

def localWord30 : Fin 32 → List (Fin 4) :=
  ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [3, 2, 3], [], [], [], [0, 1, 3, 1, 3], [], [], [], [3, 1, 3], [0, 3, 1, 3], [], [0, 3, 1, 3], [1, 3, 1, 3], [2, 3, 2, 3]]

def classIndex31 : Fin 32 → Fin 25 :=
  ![0, 0, 20, 0, 0, 0, 0, 20, 0, 20, 0, 0, 0, 0, 19, 19, 12, 12, 0, 5, 5, 0, 0, 0, 3, 2, 2, 3, 0, 0, 15, 16]

def localWord31 : Fin 32 → List (Fin 4) :=
  ![[], [], [1, 3, 2, 3], [], [], [], [], [3, 1, 3], [], [0, 3, 1, 3], [], [], [], [], [3, 1, 3], [0, 3, 1, 3], [0, 2, 3, 2, 3], [0, 3, 2, 3], [], [3], [], [], [], [], [0], [], [0], [], [], [], [3, 2, 3], [3, 2, 3]]

def classIndex (r : Index) : Fin 25 :=
  ![classIndex0, classIndex1, classIndex2, classIndex3, classIndex4, classIndex5, classIndex6, classIndex7, classIndex8, classIndex9, classIndex10, classIndex11, classIndex12, classIndex13, classIndex14, classIndex15, classIndex16, classIndex17, classIndex18, classIndex19, classIndex20, classIndex21, classIndex22, classIndex23, classIndex24, classIndex25, classIndex26, classIndex27, classIndex28, classIndex29, classIndex30, classIndex31] r.1 r.2

def localWord (r : Index) : List (Fin 4) :=
  ![localWord0, localWord1, localWord2, localWord3, localWord4, localWord5, localWord6, localWord7, localWord8, localWord9, localWord10, localWord11, localWord12, localWord13, localWord14, localWord15, localWord16, localWord17, localWord18, localWord19, localWord20, localWord21, localWord22, localWord23, localWord24, localWord25, localWord26, localWord27, localWord28, localWord29, localWord30, localWord31] r.1 r.2

def conjugator (r : Index) : StarGroup :=
  repConjugator (classIndex r) * evalWord sylowGenerator (localWord r)

private theorem fusionCheck0 : ∀ r : Fin 32,
    (element (0, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (0, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (0, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (0, r) : Equiv.Perm (Fin 24)) *
      (element (0, r) : Equiv.Perm (Fin 24)) *
      (conjugator (0, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck1 : ∀ r : Fin 32,
    (element (1, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (1, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (1, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (1, r) : Equiv.Perm (Fin 24)) *
      (element (1, r) : Equiv.Perm (Fin 24)) *
      (conjugator (1, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck2 : ∀ r : Fin 32,
    (element (2, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (2, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (2, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (2, r) : Equiv.Perm (Fin 24)) *
      (element (2, r) : Equiv.Perm (Fin 24)) *
      (conjugator (2, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck3 : ∀ r : Fin 32,
    (element (3, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (3, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (3, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (3, r) : Equiv.Perm (Fin 24)) *
      (element (3, r) : Equiv.Perm (Fin 24)) *
      (conjugator (3, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck4 : ∀ r : Fin 32,
    (element (4, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (4, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (4, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (4, r) : Equiv.Perm (Fin 24)) *
      (element (4, r) : Equiv.Perm (Fin 24)) *
      (conjugator (4, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck5 : ∀ r : Fin 32,
    (element (5, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (5, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (5, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (5, r) : Equiv.Perm (Fin 24)) *
      (element (5, r) : Equiv.Perm (Fin 24)) *
      (conjugator (5, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck6 : ∀ r : Fin 32,
    (element (6, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (6, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (6, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (6, r) : Equiv.Perm (Fin 24)) *
      (element (6, r) : Equiv.Perm (Fin 24)) *
      (conjugator (6, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck7 : ∀ r : Fin 32,
    (element (7, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (7, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (7, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (7, r) : Equiv.Perm (Fin 24)) *
      (element (7, r) : Equiv.Perm (Fin 24)) *
      (conjugator (7, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck8 : ∀ r : Fin 32,
    (element (8, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (8, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (8, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (8, r) : Equiv.Perm (Fin 24)) *
      (element (8, r) : Equiv.Perm (Fin 24)) *
      (conjugator (8, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck9 : ∀ r : Fin 32,
    (element (9, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (9, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (9, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (9, r) : Equiv.Perm (Fin 24)) *
      (element (9, r) : Equiv.Perm (Fin 24)) *
      (conjugator (9, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck10 : ∀ r : Fin 32,
    (element (10, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (10, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (10, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (10, r) : Equiv.Perm (Fin 24)) *
      (element (10, r) : Equiv.Perm (Fin 24)) *
      (conjugator (10, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck11 : ∀ r : Fin 32,
    (element (11, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (11, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (11, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (11, r) : Equiv.Perm (Fin 24)) *
      (element (11, r) : Equiv.Perm (Fin 24)) *
      (conjugator (11, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck12 : ∀ r : Fin 32,
    (element (12, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (12, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (12, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (12, r) : Equiv.Perm (Fin 24)) *
      (element (12, r) : Equiv.Perm (Fin 24)) *
      (conjugator (12, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck13 : ∀ r : Fin 32,
    (element (13, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (13, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (13, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (13, r) : Equiv.Perm (Fin 24)) *
      (element (13, r) : Equiv.Perm (Fin 24)) *
      (conjugator (13, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck14 : ∀ r : Fin 32,
    (element (14, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (14, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (14, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (14, r) : Equiv.Perm (Fin 24)) *
      (element (14, r) : Equiv.Perm (Fin 24)) *
      (conjugator (14, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck15 : ∀ r : Fin 32,
    (element (15, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (15, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (15, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (15, r) : Equiv.Perm (Fin 24)) *
      (element (15, r) : Equiv.Perm (Fin 24)) *
      (conjugator (15, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck16 : ∀ r : Fin 32,
    (element (16, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (16, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (16, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (16, r) : Equiv.Perm (Fin 24)) *
      (element (16, r) : Equiv.Perm (Fin 24)) *
      (conjugator (16, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck17 : ∀ r : Fin 32,
    (element (17, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (17, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (17, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (17, r) : Equiv.Perm (Fin 24)) *
      (element (17, r) : Equiv.Perm (Fin 24)) *
      (conjugator (17, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck18 : ∀ r : Fin 32,
    (element (18, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (18, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (18, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (18, r) : Equiv.Perm (Fin 24)) *
      (element (18, r) : Equiv.Perm (Fin 24)) *
      (conjugator (18, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck19 : ∀ r : Fin 32,
    (element (19, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (19, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (19, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (19, r) : Equiv.Perm (Fin 24)) *
      (element (19, r) : Equiv.Perm (Fin 24)) *
      (conjugator (19, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck20 : ∀ r : Fin 32,
    (element (20, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (20, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (20, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (20, r) : Equiv.Perm (Fin 24)) *
      (element (20, r) : Equiv.Perm (Fin 24)) *
      (conjugator (20, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck21 : ∀ r : Fin 32,
    (element (21, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (21, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (21, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (21, r) : Equiv.Perm (Fin 24)) *
      (element (21, r) : Equiv.Perm (Fin 24)) *
      (conjugator (21, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck22 : ∀ r : Fin 32,
    (element (22, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (22, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (22, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (22, r) : Equiv.Perm (Fin 24)) *
      (element (22, r) : Equiv.Perm (Fin 24)) *
      (conjugator (22, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck23 : ∀ r : Fin 32,
    (element (23, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (23, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (23, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (23, r) : Equiv.Perm (Fin 24)) *
      (element (23, r) : Equiv.Perm (Fin 24)) *
      (conjugator (23, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck24 : ∀ r : Fin 32,
    (element (24, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (24, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (24, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (24, r) : Equiv.Perm (Fin 24)) *
      (element (24, r) : Equiv.Perm (Fin 24)) *
      (conjugator (24, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck25 : ∀ r : Fin 32,
    (element (25, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (25, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (25, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (25, r) : Equiv.Perm (Fin 24)) *
      (element (25, r) : Equiv.Perm (Fin 24)) *
      (conjugator (25, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck26 : ∀ r : Fin 32,
    (element (26, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (26, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (26, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (26, r) : Equiv.Perm (Fin 24)) *
      (element (26, r) : Equiv.Perm (Fin 24)) *
      (conjugator (26, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck27 : ∀ r : Fin 32,
    (element (27, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (27, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (27, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (27, r) : Equiv.Perm (Fin 24)) *
      (element (27, r) : Equiv.Perm (Fin 24)) *
      (conjugator (27, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck28 : ∀ r : Fin 32,
    (element (28, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (28, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (28, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (28, r) : Equiv.Perm (Fin 24)) *
      (element (28, r) : Equiv.Perm (Fin 24)) *
      (conjugator (28, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck29 : ∀ r : Fin 32,
    (element (29, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (29, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (29, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (29, r) : Equiv.Perm (Fin 24)) *
      (element (29, r) : Equiv.Perm (Fin 24)) *
      (conjugator (29, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck30 : ∀ r : Fin 32,
    (element (30, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (30, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (30, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (30, r) : Equiv.Perm (Fin 24)) *
      (element (30, r) : Equiv.Perm (Fin 24)) *
      (conjugator (30, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

private theorem fusionCheck31 : ∀ r : Fin 32,
    (element (31, r) : Equiv.Perm (Fin 24)) = 1 ∨
    (element (31, r) : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
    (target (classIndex (31, r)) : Equiv.Perm (Fin 24)) =
      (conjugator (31, r) : Equiv.Perm (Fin 24)) *
      (element (31, r) : Equiv.Perm (Fin 24)) *
      (conjugator (31, r) : Equiv.Perm (Fin 24))⁻¹ := by
  decide +kernel

theorem checked_cases (r : Index) :
    element r = 1 ∨ (element r)^2 ≠ 1 ∨
      target (classIndex r) = conjugator r * element r * (conjugator r)⁻¹ := by
  have h : (element r : Equiv.Perm (Fin 24)) = 1 ∨
      (element r : Equiv.Perm (Fin 24))^2 ≠ 1 ∨
      (target (classIndex r) : Equiv.Perm (Fin 24)) =
        (conjugator r : Equiv.Perm (Fin 24)) * (element r : Equiv.Perm (Fin 24)) *
        (conjugator r : Equiv.Perm (Fin 24))⁻¹ := by
    rcases r with ⟨b, r⟩
    fin_cases b
    · exact fusionCheck0 r
    · exact fusionCheck1 r
    · exact fusionCheck2 r
    · exact fusionCheck3 r
    · exact fusionCheck4 r
    · exact fusionCheck5 r
    · exact fusionCheck6 r
    · exact fusionCheck7 r
    · exact fusionCheck8 r
    · exact fusionCheck9 r
    · exact fusionCheck10 r
    · exact fusionCheck11 r
    · exact fusionCheck12 r
    · exact fusionCheck13 r
    · exact fusionCheck14 r
    · exact fusionCheck15 r
    · exact fusionCheck16 r
    · exact fusionCheck17 r
    · exact fusionCheck18 r
    · exact fusionCheck19 r
    · exact fusionCheck20 r
    · exact fusionCheck21 r
    · exact fusionCheck22 r
    · exact fusionCheck23 r
    · exact fusionCheck24 r
    · exact fusionCheck25 r
    · exact fusionCheck26 r
    · exact fusionCheck27 r
    · exact fusionCheck28 r
    · exact fusionCheck29 r
    · exact fusionCheck30 r
    · exact fusionCheck31 r

  rcases h with h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (fun he => h (congrArg Subtype.val he)))
  · exact Or.inr (Or.inr (Subtype.ext h))
end Janko4.Simplicity.Max1Fusion.QuotientInvolutions.SylowFusionCertificate
