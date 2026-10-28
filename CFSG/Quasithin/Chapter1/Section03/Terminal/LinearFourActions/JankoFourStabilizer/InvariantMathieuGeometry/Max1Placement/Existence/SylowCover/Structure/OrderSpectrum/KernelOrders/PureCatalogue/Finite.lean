module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FixedCoordinates
import Mathlib.Tactic.FinCases

/-!
# Checked binary certificates for the pure J₄ kernel catalogue

The rows are checked against the four literal Sylow permutations, using the
pair-label convention for left conjugation. Twenty-two explicit local words
produce seed conjugates. Every mask outside the displayed twenty-element set
reaches one of those seed masks in at most two steps, each a conjugation or
an XOR with its conjugate. The recovery expressions and six XOR spans then
certify the small remaining lattice and its cardinalities.

These are kernel-checked arithmetic identities, not an assumed catalogue.
The connection to the actual matrix subgroups is made in `PureCatalogue`.
Source: the ATLAS max1 tables documented in `Image.StarData`; the application
is Aschbacher--Smith A.3.12, pp.47--48, and Aschbacher (1986), no.343.
The data were discovered from `KernelOrders/source/discover.py`; discovery
and witness generation are untrusted.
-/

@[expose] public section

open Janko4.Cardinality.QuotientCount.Image Janko4.Cardinality.KernelCount
open Janko4.LocalStructure.SylowCore
open Janko4.Simplicity.Max1Fusion.QuotientInvolutions
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureCertificate

def rows : Fin 4 → Fin 11 → ℕ :=
  ![![898, 2, 8, 4, 16, 991, 959, 883, 1131, 1819, 740],
    ![1572, 256, 1046, 439, 1345, 1484, 1637, 949, 2, 392, 83],
    ![1186, 83, 750, 1084, 1742, 667, 573, 70, 1865, 1637, 655],
    ![1, 1838, 43, 495, 503, 1732, 806, 1253, 2020, 1637, 429]]

theorem rows_eq : ∀ i j, rows i j =
    pairLabel ((sylowGenerator i).val (basisPair j).1)
      ((sylowGenerator i).val (basisPair j).2) := by decide +kernel

def step (s m : ℕ) : ℕ :=
  if h : s < 4 then maskImage (rows ⟨s, h⟩) m
  else if h : s < 8 then m ^^^ maskImage (rows ⟨s - 4, by omega⟩) m
  else m

def seeds : List ℕ := [47, 81, 112, 124, 151, 456, 637, 686, 699, 841, 899, 911, 1125, 1187, 1303, 1307, 1410, 1609, 1679, 1764, 1768, 1795]
def allowed : List ℕ := [0, 198, 370, 436, 571, 583, 641, 765, 821, 1011, 1049, 1247, 1387, 1453, 1630, 1688, 1836, 1872, 1942, 2026]

def wordMask : List Bool → ℕ
  | [] => 1
  | b :: bs => maskImage (if b then yMasks else xMasks) (wordMask bs)

def seedWords : Fin 22 → List Bool :=
  ![[false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true],
    [true, false, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true],
    [true, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true],
    [true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true],
    [true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true],
    [false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true],
    [true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true, false, true, true, false, true],
    [true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, true, false, true],
    [true, false, true, true, false, true, false, true, true, false, true, false, true, true, false, true],
    [true, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true],
    [true, true, false, true, false, true, false, true, false, true, true, false, true],
    [true, true, false, true, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true],
    [false, true, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true],
    [true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true],
    [true, true, false, true, false, true, true, false, true, true, false, true],
    [false, true, false, true, false, true, false, true, false, true, true, false, true, true, false, true],
    [false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true],
    [false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true],
    [false, true, false, true, false, true, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true],
    [false, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true],
    [false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, true, false, true],
    [true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true]]

theorem seed_words : ∀ i : Fin 22, wordMask (seedWords i) = seeds[i.val] := by
  decide +kernel

def witness : Fin 32 → Fin 64 → ℕ :=
  ![![80, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 8, 63, 80, 62, 44, 71, 44, 62, 44, 26, 44, 62, 44, 71, 44, 62, 44, 63, 44],
    ![62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 65, 44, 62, 44, 71, 44, 62, 80, 63, 8, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 80, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 80, 44, 62, 44],
    ![71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 65, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 80, 71, 44, 62, 44, 64, 44, 62, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 26, 44, 17, 44, 62, 44, 71, 44],
    ![62, 44, 71, 44, 62, 44, 80, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 8, 71, 44, 62, 44, 65, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44],
    ![62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 8, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 29, 44, 62, 44, 71, 44, 62, 44],
    ![71, 44, 62, 44, 65, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 80, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 35, 44],
    ![62, 44, 65, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 80, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44],
    ![63, 44, 62, 44, 71, 44, 62, 44, 80, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 65, 44],
    ![44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 29, 44, 62, 44, 71, 44, 62, 8, 63, 35, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 26, 44, 80, 44, 62, 44, 71],
    ![44, 62, 44, 71, 44, 62, 44, 80, 44, 62, 44, 35, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 65, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 80, 44, 62],
    ![44, 80, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 80, 63, 44, 62, 44, 71, 44, 62, 44, 65, 44, 62, 44, 80, 44, 62, 44, 63],
    ![44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 65, 44, 62, 44, 71, 35, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 71, 44, 62, 17, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 80, 44, 62],
    ![44, 62, 44, 65, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 80, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62],
    ![44, 63, 44, 62, 44, 71, 44, 62, 44, 80, 44, 62, 44, 71, 44, 62, 17, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 35, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 65],
    ![44, 62, 44, 80, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 80, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 35, 44, 62, 44, 65, 44, 62, 44, 71, 44, 62],
    ![44, 71, 44, 62, 44, 26, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 80, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71],
    ![44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 35, 44, 62, 44, 80, 44, 62, 44, 71, 44, 62, 44, 62, 44, 8, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 65, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64],
    ![44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 65, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 71, 44, 62, 44, 80, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62],
    ![44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 29, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 62, 44, 80, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71],
    ![44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 80, 44, 63, 44, 62, 44, 8, 44, 62, 44, 65, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62],
    ![8, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 80, 44, 62, 44, 80, 44, 62, 44, 63, 44, 65, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62],
    ![44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 65, 44, 62, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 80, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71],
    ![44, 62, 80, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 26, 44, 62, 44, 71, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 80, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62],
    ![44, 64, 44, 62, 44, 71, 8, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 17, 44, 26, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 62, 44, 71, 44, 62, 44, 65, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 8, 63],
    ![71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 65, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 62, 44, 17, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44],
    ![62, 44, 71, 44, 62, 44, 63, 44, 62, 80, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 80, 44, 63, 44, 62, 44, 71, 44, 62, 44, 26, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44],
    ![63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 80, 63, 44, 62, 44, 71, 44, 62, 44, 80, 44, 62, 44, 71, 44, 62, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 65, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44],
    ![62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 65, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 71, 44, 62, 44, 80, 44, 62, 44, 80, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 17, 62, 44],
    ![62, 44, 63, 80, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 65, 44, 62, 44, 71, 44, 35, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 80, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44],
    ![64, 44, 62, 44, 71, 44, 62, 44, 63, 17, 62, 44, 71, 44, 62, 44, 80, 44, 26, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 62, 44, 71, 44, 62, 44, 65, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44],
    ![62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 80, 44, 62, 44, 71, 44, 62, 44, 63, 44, 29, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 8, 62, 44, 71, 44, 62, 44],
    ![71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 65, 44, 62, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 80, 44, 62, 44, 71, 44, 62, 44, 63, 44, 62, 44, 71, 44, 62, 44, 64, 44, 62, 44, 71, 44]]

def Valid (b : Fin 32) (i : Fin 64) : Prop :=
  64 * b.val + i.val ∈ allowed ∨
    step (witness b i / 9) (step (witness b i % 9) (64 * b.val + i.val)) ∈ seeds

instance (b : Fin 32) (i : Fin 64) : Decidable (Valid b i) :=
  inferInstanceAs (Decidable (_ ∨ _))

set_option maxRecDepth 10000 in
theorem certificate : ∀ b : Fin 32, ∀ i : Fin 64, Valid b i := by
  intro b
  fin_cases b <;> decide +kernel

def basisRows : Fin 6 → List ℕ :=
  ![[], [198], [1387, 198], [1387, 571, 198], [1387, 821, 198], [1049, 583, 370, 198]]

def xorSpan : List ℕ → List ℕ
  | [] => [0]
  | x :: xs => xorSpan xs ++ (xorSpan xs).map (fun y => x ^^^ y)

def spanMasks (i : Fin 6) : List ℕ := xorSpan (basisRows i)

theorem span_zero : ∀ i, 0 ∈ spanMasks i := by decide +kernel

theorem span_rows : ∀ i, ∀ m ∈ basisRows i, m ∈ spanMasks i := by decide +kernel

theorem span_lt : ∀ i, ∀ m ∈ spanMasks i, m < 2048 := by decide +kernel

theorem span_xor : ∀ i, ∀ m ∈ spanMasks i, ∀ n ∈ spanMasks i,
    m ^^^ n ∈ spanMasks i := by decide +kernel

theorem span_card : ∀ i, (spanMasks i).toFinset.card = 2 ^ (basisRows i).length := by
  decide +kernel

def representatives : Fin 6 → ℕ := ![0, 198, 1387, 571, 821, 370]

inductive Expression where
  | source
  | xor (e f : Expression)
  | act (i : Fin 4) (e : Expression)

def evaluate (m : ℕ) : Expression → ℕ
  | .source => m
  | .xor e f => evaluate m e ^^^ evaluate m f
  | .act i e => maskImage (rows i) (evaluate m e)

def lowerExpressions : Fin 6 → List Expression :=
  ![[],
    [.source],
    [.source, (.xor .source (.act 2 .source))],
    [(.xor .source (.act 0 .source)), .source, (.xor .source (.act 2 .source))],
    [(.act 2 (.xor .source (.act 3 .source))), .source, (.xor (.act 3 .source) (.act 2 (.act 3 .source)))],
    [(.act 0 .source), (.act 1 (.act 3 .source)), .source, (.xor (.act 0 .source) (.act 3 .source))]]

theorem lower_certificate : ∀ i,
    (lowerExpressions i).map (evaluate (representatives i)) = basisRows i := by
  decide +kernel

def recoveryTag : Fin 20 → Fin 6 := ![0, 1, 5, 5, 3, 5, 5, 3, 4, 4, 5, 5, 2, 2, 4, 4, 5, 3, 3, 5]

def recoveryExpression : Fin 20 → Expression :=
  ![.source,
    .source,
    .source,
    (.act 3 (.act 0 .source)),
    .source,
    (.act 3 (.act 1 .source)),
    (.act 1 (.act 0 .source)),
    (.act 2 .source),
    .source,
    (.act 3 (.act 2 (.act 3 .source))),
    (.act 0 .source),
    (.act 3 .source),
    .source,
    (.act 2 .source),
    (.act 3 (.act 2 .source)),
    (.act 3 .source),
    (.act 1 (.act 2 .source)),
    (.act 0 .source),
    (.act 1 .source),
    (.act 1 .source)]

theorem recovery_certificate : ∀ j : Fin 20,
    evaluate allowed[j.val] (recoveryExpression j) = representatives (recoveryTag j) ∧
      allowed[j.val] ∈ spanMasks (recoveryTag j) := by decide +kernel

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureCertificate
