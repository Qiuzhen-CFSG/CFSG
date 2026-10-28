module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics
import Mathlib.Tactic.FinCases

/-!
# Three-coset witnesses for the second Tits parabolic

The representatives are the first three powers of `s8 * r8`. For each of the
nine generators, the table gives the destination coset and a Sylow normal-form
factor. The companion row modules check every word equality on all 1600 points by the kernel.
The inverse destination table permits the inverse transitions to be deduced
by group algebra, avoiding a second set of permutation certificates.

The tables are witnesses computed from the Atlas permutations; their validity
is proved here, independently of GAP. The generators and normal-form conventions
are Parrott (1972), p. 683, as transcribed in
`refs/original/n-group-global/parrott-tits-presentation.md`.
-/

@[expose] public section

namespace Tits.RelativeSecondBlockLayers.SecondOrder
open Atlas1600OrderCertificate

def generatorIndex : Fin 9 → ParrottGenerator :=
  ![.r8, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8]
def generator (a : Fin 9) : Atlas1600Group :=
  atlas1600ParrottAssignment (generatorIndex a)
def rep (i : Fin 3) : Atlas1600Group :=
  (atlas1600ParrottAssignment .s8 * atlas1600ParrottAssignment .r8) ^ i.val
def dest : Fin 9 → Fin 3 → Fin 3 :=
  ![![1, 0, 2],
    ![0, 1, 2],
    ![0, 1, 2],
    ![0, 1, 2],
    ![0, 1, 2],
    ![0, 1, 2],
    ![0, 1, 2],
    ![0, 1, 2],
    ![0, 2, 1]]
def factor : Fin 9 → Fin 3 → Fin 2048 :=
  ![![1024, 1024, 1024],
    ![1, 757, 602],
    ![2, 128, 146],
    ![4, 1019, 374],
    ![16, 16, 16],
    ![32, 919, 400],
    ![128, 146, 2],
    ![256, 243, 910],
    ![1024, 1024, 1024]]
def destInverse : Fin 9 → Fin 3 → Fin 3 :=
  ![![1, 0, 2],
    ![0, 1, 2],
    ![0, 1, 2],
    ![0, 1, 2],
    ![0, 1, 2],
    ![0, 1, 2],
    ![0, 1, 2],
    ![0, 1, 2],
    ![0, 2, 1]]

theorem dest_inverse (a : Fin 9) (i : Fin 3) : dest a (destInverse a i) = i := by
  revert a i
  decide +kernel


end Tits.RelativeSecondBlockLayers.SecondOrder
