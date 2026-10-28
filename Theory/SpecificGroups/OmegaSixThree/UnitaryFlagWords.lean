module
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.SplitMarking
public import Theory.SpecificGroups.OmegaSixThree.UnitaryVertex
import all Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.SplitMarking
import all Theory.SpecificGroups.OmegaSixThree.VertexComparison
open Matrix Atlas.Algebra
open Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo
open Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison
/-!
# Checked words for the F.5 unitary flag

Six short words in the matched exceptional generators give the long and short
root matrices, an explicit flag adjustment, and the three adjacent generators
of the ordinary fixed-plane S₄. Both the unitary matrices and their ternary
symplectic images are kernel checked. These equations retain the original
matrix flag when constructing the F.5.7 local and vertex comparison.

Source: Aschbacher–Smith F.5.1–3 and F.5.7, printed pp.300–303.
-/
@[expose] public noncomputable section
namespace OmegaSixThree.VertexComparison.FlagWords

def letters : Fin 6 → List (Fin 2 × Bool) :=
  ![[(0, false), (1, false), (0, true), (1, true), (0, false), (1, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, true), (1, false)],
    [(1, false), (0, false), (1, false), (0, true), (1, true), (0, false), (1, true)],
    [(0, false), (1, false), (0, true), (1, true), (0, false), (1, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (1, true), (0, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (1, true)],
    [(0, true), (1, true), (1, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true)],
    [(0, false), (1, false), (0, true), (1, true), (0, false), (1, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, true)],
    [(0, true), (1, false), (0, false), (1, true), (0, true)]]
def evaluate {G : Type*} [Group G] (g : Fin 2 → G) (i : Fin 6) : G :=
  ((letters i).map (fun a => if a.2 then (g a.1)⁻¹ else g a.1)).prod

theorem map_evaluate {G K : Type*} [Group G] [Group K] (f : G →* K)
    (g : Fin 2 → G) (i : Fin 6) :
    f (evaluate g i) = evaluate (fun j => f (g j)) i := by
  simp only [evaluate,map_list_prod,List.map_map]
  congr 2
  funext a
  split <;> simp_all

def splitElement (i : Fin 6) : SplitMarking.splitForm.specialSubgroup :=
  SplitMarking.splitEquivStandard.symm (evaluate unitaryGenerator i)

def splitMatrix : Fin 6 → Matrix (Fin 4) (Fin 4) GoldenFour :=
  ![!![1,0,0,1; 0,1,0,0; 0,0,1,0; 0,0,0,1],
    !![1,0,1,0; 0,1,0,1; 0,0,1,0; 0,0,0,1],
    !![1,0,0,0; 0,1,0,0; 0,1,1,0; 0,0,0,1],
    !![1,1,1,0; 0,1,0,1; 0,0,1,1; 0,0,0,1],
    !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0],
    !![1,1,0,0; 0,1,0,0; 0,0,1,1; 0,0,0,1]]
theorem splitElement_matrix (i : Fin 6) : (splitElement i).val.val = splitMatrix i := by
  change (SplitMarking.splitEquivStandard.symm _).val.val = _
  rw [SplitMarking.splitEquivStandard_symm_val]
  revert i
  decide +kernel

def spMatrix : Fin 6 → Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  ![!![0,2,0,0; 2,0,0,0; 0,0,0,2; 0,0,2,0],
    !![1,0,0,1; 0,1,1,0; 0,1,2,0; 1,0,0,2],
    !![1,2,0,2; 1,2,1,0; 0,1,1,1; 2,0,2,2],
    !![0,0,1,0; 0,0,0,1; 2,0,0,0; 0,2,0,0],
    !![2,0,0,1; 0,2,1,1; 2,1,1,0; 1,0,0,1],
    !![2,0,0,1; 0,2,1,0; 0,1,1,0; 1,0,0,1]]
theorem spWord_matrix (i : Fin 6) :
    (OmegaSixThree.VertexComparison.spToSL (evaluate symplecticGenerator i)).val = spMatrix i := by
  revert i
  decide +kernel
end OmegaSixThree.VertexComparison.FlagWords
