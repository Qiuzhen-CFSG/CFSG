/-
The Golay basis and marked Witt/Leech coordinates used here are those of
Gerald Höhn, ATLAS revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
The imported sources retain the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.HigmanSimsGraph
public import Theory.SpecificGroups.J2HSMultipliers.HSModelComparison.Graph
public import Theory.AtlasPort.OtherSporadic.Codes.GolayBasis

/-!
# A checked isomorphism from the permutation graph to the Leech graph

The marked Golay coordinates give 22 point labels and 77 octad witnesses.
Their supports are proved to be distinct heptads through the second marked
coordinate. The displayed vertex matching preserves every adjacency pair.
The existing Witt-to-Leech isomorphism then identifies the actual graphs.

The finite data were discovered by `source/discover.py`; every assertion used
here is proved in Lean's kernel. The coordinate convention, witness format,
and source references are recorded in `source/README.md`.
-/

@[expose] public section

open Atlas.Codes Atlas.Conway
open Sporadic.LeechRelated.HS.OrderCertificate
namespace Sporadic.LeechRelated.HS.ModelComparison.WittCertificate
set_option maxRecDepth 10000

def coordinate (i : Fin 24) : Omega := ![((0, 0), 0), ((0, 0), 1), ((0, 0), 2), ((0, 0), 3), ((0, 1), 0), ((0, 1), 1), ((0, 1), 2), ((0, 1), 3), ((1, 0), 0), ((1, 0), 1), ((1, 0), 2), ((1, 0), 3), ((1, 1), 0), ((1, 1), 1), ((1, 1), 2), ((1, 1), 3), ((2, 0), 0), ((2, 0), 1), ((2, 0), 2), ((2, 0), 3), ((2, 1), 0), ((2, 1), 1), ((2, 1), 2), ((2, 1), 3)] i

theorem coordinate_injective : Function.Injective coordinate := by
  have h : ∀ i j : Fin 24, coordinate i = coordinate j → i = j := by decide +kernel
  exact h

def puncturedCoordinate (i : Fin 23) : Mathieu23Points co3MarkedCoordinate :=
  ⟨coordinate i.succ, by
    have h : ∀ i : Fin 23, coordinate i.succ ≠ co3MarkedCoordinate := by decide +kernel
    exact h i⟩

def pointLabel (i : Fin 22) : HSPointLabels :=
  ⟨puncturedCoordinate i.succ, by
    have h : ∀ i : Fin 22, puncturedCoordinate i.succ ≠ co3BasePoint := by decide +kernel
    exact h i⟩

theorem pointLabel_injective : Function.Injective pointLabel := by
  intro i j h
  have hc : coordinate i.succ.succ = coordinate j.succ.succ :=
    congrArg (fun p : HSPointLabels => p.val.val) h
  exact Fin.succ_inj.mp (Fin.succ_inj.mp (coordinate_injective hc))

def octadMasks : List ℕ := [255, 3855, 13107, 15555, 50115, 52275, 61455, 218371, 240131, 352419, 364627, 394899, 395619, 591459, 592275, 680019, 692387, 809475, 828675, 983055, 1132615, 1148043, 1184331, 1188231, 1315879, 1320987, 1589547, 1606167, 2167431, 2171211, 2246795, 2262087, 2375959, 2392619, 2626587, 2631719, 3171843, 3184899, 3342387, 3932355, 4266027, 4269079, 4342311, 4358427, 4473931, 4491399, 4723015, 4727435, 5263507, 5283939, 5571331, 5901315, 6292899, 6294099, 6696963, 6930435, 8471067, 8487207, 8525847, 8528939, 8655243, 8659527, 8930439, 8947787, 9438547, 9439907, 9879555, 10039299, 10506339, 10526867, 10816515, 11141891, 12609795, 12621315, 12779715, 13369395, 15728655]

def coefficientMasks : List ℕ := [64, 128, 456, 264, 136, 72, 256, 898, 514, 571, 891, 113, 177, 561, 753, 123, 315, 258, 130, 512, 3523, 3531, 3777, 3913, 3824, 4024, 3954, 4026, 2257, 2393, 3027, 3035, 2850, 3050, 2720, 3048, 1050, 1434, 1616, 1040, 2292, 2492, 3062, 2878, 3015, 3023, 2629, 3021, 1399, 1079, 1668, 1028, 165, 101, 284, 540, 2470, 2414, 2724, 3052, 2645, 3037, 3031, 3039, 1253, 1061, 1052, 1820, 311, 119, 516, 132, 154, 282, 528, 80, 1024]

def heptad (i : Fin 77) : Finset (Mathieu23Points co3MarkedCoordinate) :=
  ((Finset.univ : Finset (Fin 23)).filter
    (fun j => (octadMasks[i.val]! >>> (j.val + 1)) % 2 = 1)).image puncturedCoordinate

def octad (i : Fin 77) : Finset Omega :=
  insert co3MarkedCoordinate (mathieu23BlockLift co3MarkedCoordinate (heptad i))

def word (i : Fin 77) : BinaryWord :=
  ∑ j : Fin 12, if (coefficientMasks[i.val]! >>> j.val) % 2 = 1 then golayGenerators j else 0

theorem word_mem (i : Fin 77) : word i ∈ golay := by
  apply golay.sum_mem
  intro j _
  split
  · rw [← golayBasis_coe]
    exact (golayBasis j).property
  · exact golay.zero_mem

theorem word_support (i : Fin 77) : support (word i) = octad i := by
  ext p
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
  have h : ∀ i : Fin 77, ∀ p : Omega, word i p ≠ 0 ↔ p ∈ octad i := by
    apply allFin
    decide +kernel
  exact h i p

theorem octad_card (i : Fin 77) : (octad i).card = 8 := by
  have h : ∀ i : Fin 77, (octad i).card = 8 := by
    apply allFin
    decide +kernel
  exact h i

theorem octad_mem (i : Fin 77) : octad i ∈ octads := by
  apply (octads_mem _).mpr
  refine ⟨⟨word i, word_mem i⟩, ?_, word_support i⟩
  change (support (word i)).card = 8
  rw [word_support, octad_card]

theorem base_mem_heptad (i : Fin 77) : co3BasePoint ∈ heptad i := by
  have h : ∀ i : Fin 77, co3BasePoint ∈ heptad i := by
    apply allFin
    decide +kernel
  exact h i

def hexadLabel (i : Fin 77) : HSHexadLabels :=
  ⟨⟨heptad i, (mathieu23Blocks_mem _ _).mpr (octad_mem i)⟩, base_mem_heptad i⟩

theorem hexadLabel_injective : Function.Injective hexadLabel := by
  have h : ∀ i j : Fin 77, heptad i = heptad j → i = j := by
    apply allFin
    decide +kernel
  intro i j he
  exact h i j (congrArg (fun B : HSHexadLabels => B.val.val) he)

abbrev Label := Unit ⊕ (Fin 22 ⊕ Fin 77)

def labelVertex : Label → HSWittVertices := Sum.map id (Sum.map pointLabel hexadLabel)

theorem labelVertex_injective : Function.Injective labelVertex :=
  Function.injective_id.sumMap (pointLabel_injective.sumMap hexadLabel_injective)

def labelAdj : Label → Label → Prop
  | .inl _, .inr (.inl _) => True
  | .inr (.inl _), .inl _ => True
  | .inr (.inl i), .inr (.inr j) => (pointLabel i).val ∈ heptad j
  | .inr (.inr i), .inr (.inl j) => (pointLabel j).val ∈ heptad i
  | .inr (.inr i), .inr (.inr j) => (heptad i ∩ heptad j).card = 1
  | _, _ => False

instance labelAdjDecidable : DecidableRel labelAdj := by
  rintro (x | (x | x)) (y | (y | y)) <;> unfold labelAdj <;> infer_instance

theorem labelVertex_adj (x y : Label) :
    hsWittGraph.Adj (labelVertex x) (labelVertex y) ↔ labelAdj x y := by
  rcases x with x | (x | x) <;> rcases y with y | (y | y)
  · cases x; cases y
    exact iff_of_false (hsWittGraph.loopless.irrefl _) id
  · exact iff_of_true (hs_witt_base_point _) trivial
  · exact iff_of_false (hs_witt_base_hexad _) id
  · exact iff_of_true (hs_witt_base_point _).symm trivial
  · exact iff_of_false (hs_witt_points_nonadjacent _ _) id
  · exact hs_witt_point_hexad _ _
  · exact iff_of_false (fun h => hs_witt_base_hexad _ h.symm) id
  · exact (hsWittGraph.adj_comm _ _).trans (hs_witt_point_hexad _ _)
  · exact hs_witt_hexads_adjacent _ _

def labels (i : Fin 100) : Label :=
  ![.inl (),
    .inr (.inr 69),
    .inr (.inr 0),
    .inr (.inr 2),
    .inr (.inl 0),
    .inr (.inr 33),
    .inr (.inr 73),
    .inr (.inr 48),
    .inr (.inl 1),
    .inr (.inl 3),
    .inr (.inl 7),
    .inr (.inl 21),
    .inr (.inl 18),
    .inr (.inr 25),
    .inr (.inr 58),
    .inr (.inr 15),
    .inr (.inr 49),
    .inr (.inr 40),
    .inr (.inr 31),
    .inr (.inr 30),
    .inr (.inr 20),
    .inr (.inr 59),
    .inr (.inr 43),
    .inr (.inr 38),
    .inr (.inr 50),
    .inr (.inr 62),
    .inr (.inl 15),
    .inr (.inr 70),
    .inr (.inl 8),
    .inr (.inr 18),
    .inr (.inr 55),
    .inr (.inr 4),
    .inr (.inl 13),
    .inr (.inr 41),
    .inr (.inr 72),
    .inr (.inr 1),
    .inr (.inr 3),
    .inr (.inr 12),
    .inr (.inl 5),
    .inr (.inl 20),
    .inr (.inl 12),
    .inr (.inr 11),
    .inr (.inr 24),
    .inr (.inr 6),
    .inr (.inl 16),
    .inr (.inr 37),
    .inr (.inr 51),
    .inr (.inl 4),
    .inr (.inr 9),
    .inr (.inl 2),
    .inr (.inl 19),
    .inr (.inr 8),
    .inr (.inl 11),
    .inr (.inr 16),
    .inr (.inr 57),
    .inr (.inr 44),
    .inr (.inr 52),
    .inr (.inr 7),
    .inr (.inr 34),
    .inr (.inr 42),
    .inr (.inr 60),
    .inr (.inr 22),
    .inr (.inr 10),
    .inr (.inr 28),
    .inr (.inr 32),
    .inr (.inr 64),
    .inr (.inl 17),
    .inr (.inl 9),
    .inr (.inr 61),
    .inr (.inr 26),
    .inr (.inl 14),
    .inr (.inl 6),
    .inr (.inr 23),
    .inr (.inr 29),
    .inr (.inr 13),
    .inr (.inr 36),
    .inr (.inr 63),
    .inr (.inr 56),
    .inr (.inr 17),
    .inr (.inr 27),
    .inr (.inr 65),
    .inr (.inr 67),
    .inr (.inr 46),
    .inr (.inr 19),
    .inr (.inr 53),
    .inr (.inr 68),
    .inr (.inr 35),
    .inr (.inr 21),
    .inr (.inr 39),
    .inr (.inr 71),
    .inr (.inr 75),
    .inr (.inl 10),
    .inr (.inr 74),
    .inr (.inr 76),
    .inr (.inr 5),
    .inr (.inr 54),
    .inr (.inr 66),
    .inr (.inr 45),
    .inr (.inr 14),
    .inr (.inr 47)] i

theorem labels_injective : Function.Injective labels := by
  have h : ∀ i j : Fin 100, labels i = labels j → i = j := by
    apply allFin
    decide +kernel
  exact h

def vertex (i : Fin 100) : HSWittVertices := labelVertex (labels i)

theorem vertex_injective : Function.Injective vertex :=
  labelVertex_injective.comp labels_injective

noncomputable def vertexEquiv : Fin 100 ≃ HSWittVertices :=
  Equiv.ofBijective vertex ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨vertex_injective, by
      rw [Nat.card_fin, Nat.card_sum, Nat.card_sum, hs_point_labels_card, hs_hexad_labels_card]
      simp⟩)

theorem vertex_adj (x y : Fin 100) :
    hsWittGraph.Adj (vertex x) (vertex y) ↔ permutationGraph.Adj x y := by
  have h : ∀ x y : Fin 100, labelAdj (labels x) (labels y) ↔ NormalizerIndex.adjacency x y := by
    apply allFin
    decide +kernel
  exact (labelVertex_adj (labels x) (labels y)).trans (h x y)

noncomputable def wittGraphEquiv : permutationGraph ≃g hsWittGraph where
  toEquiv := vertexEquiv
  map_rel_iff' := by intro x y; exact vertex_adj x y

noncomputable def graphEquiv : permutationGraph ≃g Atlas.Sporadic.HigmanSims.graph :=
  wittGraphEquiv.trans Atlas.Sporadic.HigmanSims.wittGraphEquiv

end Sporadic.LeechRelated.HS.ModelComparison.WittCertificate
