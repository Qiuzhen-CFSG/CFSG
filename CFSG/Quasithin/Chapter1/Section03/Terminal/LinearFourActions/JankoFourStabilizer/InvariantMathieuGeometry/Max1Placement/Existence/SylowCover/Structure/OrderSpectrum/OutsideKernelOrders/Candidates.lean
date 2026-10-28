module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.RankInvariant

/-!
# Literal candidates for the outside-kernel elementary subgroups

These nine subgroups are specified by ascending products in the existing
21-generator presentation and its literal matrix words. They are candidate
subgroups, not an asserted exhaustive table. The kernel words are the eleven
marked basis elements in the same candidate coordinates; their equality with
the actual Mathieu kernel is a separate matrix calculation.

The finite rank tests select proper invariant subgroups in discovery data.
The definitions below fix the precise proof obligations, without accepting
GAP or Python output as evidence. See `source/README.md` for reproducibility.
Source context: Aschbacher–Smith A.3.12, pp.47–48; Kleidman–Wilson (1988).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders
open Janko4 Subgroup Janko4.LocalStructure.SylowNormalEights
attribute [local irreducible] modelGroup matrixA matrixB

/-- The nine candidate generating lists, using zero-based ascending PC words. -/
def candidateWords : Fin 9 → List (List (Fin 21)) :=
  ![[[15, 17], [16], [18], [19], [20]],
    [[15], [16], [18], [19], [20]],
    [[14, 15], [16], [17], [18], [19], [20]],
    [[9, 15], [14], [16], [17], [18], [19], [20]],
    [[11, 13], [14, 15], [16], [17], [18], [19], [20]],
    [[15], [16], [17], [18], [19], [20]],
    [[13], [15], [16], [17], [18], [19], [20]],
    [[14], [15], [16], [17], [18], [19], [20]],
    [[9], [14], [15], [16], [17], [18], [19], [20]]]

/-- Candidate coordinates for the eleven literal kernel generators. -/
def kernelWords : List (List (Fin 21)) :=
  [[0, 3, 5, 6, 8, 10, 14, 17, 18, 19, 20], [6, 11, 14, 16, 18, 20], [0, 5, 6, 8, 10, 12, 13, 15, 19, 20], [0, 5, 6, 8, 9, 10, 12, 13, 15, 18, 19], [3, 6, 11, 12, 13, 15, 16, 17, 18, 19, 20], [0, 3, 5, 6, 8, 9, 10, 11, 16, 19, 20], [0, 5, 8, 10, 11, 12, 13, 15, 16, 17, 19], [14, 17, 18, 20], [6, 9, 11, 14, 16, 17, 18, 19], [0, 3, 5, 6, 8, 10, 16, 17, 19, 20], [6, 9, 14, 17, 18, 20]]

/-- Generated subgroup of the evaluations of a finite list of words. -/
def wordSubgroup {G : Type*} [Group G] (g : Fin 21 → G)
    (ws : List (List (Fin 21))) : Subgroup G :=
  closure (Set.range (fun w : {w : List (Fin 21) // w ∈ ws} => (w.val.map g).prod))

/-- Word evaluation and generated subgroups commute with genuine homomorphisms. -/
theorem map_wordSubgroup {G H : Type*} [Group G] [Group H]
    (g : Fin 21 → G) (ws : List (List (Fin 21))) (f : G →* H) :
    (wordSubgroup g ws).map f = wordSubgroup (fun i => f (g i)) ws := by
  unfold wordSubgroup
  rw [MonoidHom.map_closure, ← Set.range_comp]
  congr 2
  funext w
  simp only [Function.comp_apply, map_list_prod, List.map_map, Function.comp_def]

/-- The nine candidates in the universal presentation. -/
def abstractFamily (i : Fin 9) : Subgroup Presentation.Carrier :=
  wordSubgroup Presentation.generator (candidateWords i)

/-- The marked kernel in the universal presentation. -/
def abstractKernel : Subgroup Presentation.Carrier :=
  wordSubgroup Presentation.generator kernelWords

/-- The very same candidate words in the original J₄ model. -/
noncomputable def matrixFamily (i : Fin 9) : Subgroup Model :=
  wordSubgroup (fun j => (MatrixWords.pcGenerator j : Model)) (candidateWords i)

/-- The same kernel words in the original J₄ model; actual identification is still required. -/
noncomputable def matrixKernel : Subgroup Model :=
  wordSubgroup (fun j => (MatrixWords.pcGenerator j : Model)) kernelWords

/-- Exhaustion of normal elementary subgroups outside the marked kernel.
The order premise of its eventual producer is discharged by matrix realization. -/
def OutsideCatalogue : Prop :=
  ∀ A : Subgroup Presentation.Carrier, A.Normal → IsElementaryAbelian 2 A →
    ¬ A ≤ abstractKernel → ∃ i : Fin 9, A = abstractFamily i

/-- An honest realization, followed by the literal inclusion in J₄. -/
noncomputable def ambientRealization
    (hr : Presentation.Relations MatrixWords.pcGenerator)
    (hg : closure (Set.range MatrixWords.pcGenerator) = ⊤) : Presentation.Carrier →* Model :=
  OuterReduction.OddIndex.twoSubgroup.subtype.comp (matrixEquivOfWords hr hg).toMonoidHom

theorem ambientRealization_injective
    (hr : Presentation.Relations MatrixWords.pcGenerator)
    (hg : closure (Set.range MatrixWords.pcGenerator) = ⊤) :
    Function.Injective (ambientRealization hr hg) :=
  Subtype.val_injective.comp (matrixEquivOfWords hr hg).injective

@[simp] theorem ambientRealization_generator
    (hr : Presentation.Relations MatrixWords.pcGenerator)
    (hg : closure (Set.range MatrixWords.pcGenerator) = ⊤) (j : Fin 21) :
    ambientRealization hr hg (Presentation.generator j) = (MatrixWords.pcGenerator j : Model) :=
  congrArg Subtype.val (matrixEquivOfRelations_generator _ hr hg j)

/-- The family comparison uses the literal generator equations, not equality of orders. -/
theorem map_abstractFamily
    (hr : Presentation.Relations MatrixWords.pcGenerator)
    (hg : closure (Set.range MatrixWords.pcGenerator) = ⊤) (i : Fin 9) :
    (abstractFamily i).map (ambientRealization hr hg) = matrixFamily i := by
  simp only [abstractFamily, map_wordSubgroup, ambientRealization_generator, matrixFamily]

/-- The marked kernel is transported by the identical word comparison. -/
theorem map_abstractKernel
    (hr : Presentation.Relations MatrixWords.pcGenerator)
    (hg : closure (Set.range MatrixWords.pcGenerator) = ⊤) :
    abstractKernel.map (ambientRealization hr hg) = matrixKernel := by
  simp only [abstractKernel, map_wordSubgroup, ambientRealization_generator, matrixKernel]

/-- First five fibers use single ranks; the last four count rank-16 pairs. -/
def candidateTest : Fin 9 → RankTest :=
  ![.displacement 50, .displacement 56, .displacement 50,
    .displacement 50, .displacement 50, .pairCount 16 34,
    .pairCount 16 66, .pairCount 16 58, .pairCount 16 58]

def candidateOrder : Fin 9 → ℕ := ![32, 32, 64, 128, 128, 64, 128, 128, 256]

def candidateSpanOrder : Fin 9 → ℕ := ![8, 16, 32, 64, 32, 4, 4, 2, 8]

/-- Exact finite cardinal certificates for the actual matrix subgroups and fiber spans. -/
def RankCertificates : Prop :=
  ∀ i : Fin 9, Nat.card (matrixFamily i) = candidateOrder i ∧
    Nat.card (rankSpan (matrixFamily i) (candidateTest i)) = candidateSpanOrder i

theorem candidateSpanOrder_bounds (i : Fin 9) :
    1 < candidateSpanOrder i ∧ candidateSpanOrder i < candidateOrder i := by
  exact (by decide : ∀ i : Fin 9,
    1 < candidateSpanOrder i ∧ candidateSpanOrder i < candidateOrder i) i

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders
