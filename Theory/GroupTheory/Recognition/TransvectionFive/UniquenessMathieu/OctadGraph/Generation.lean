module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Action
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineLifts.Generators
import all Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineLifts.Generators

/-!
# Generation and local edges in the native octad geometry

Words in five elements of the plane–point stabilizer and two elements of the
pointwise edge fixer carry the marked second octad to all thirty neighbors
of the first. Orbit–stabilizer then gives the vertex generation identity.
Adding a literal edge reversal to the plane–point elements reaches all fifteen
plane octads and all ninety directed plane edges. The same argument gives
local generation and identifies every plane edge with a local edge orbit.

Only these small orbit certificates are checked, not an enumeration of M24.
The point tables reuse the native Sylow generators and the native affine trio
lifts. The latter's private bodies are imported solely inside this certificate
module to check the tables; no private name enters its public interface.
The untrusted search is recorded in `Generation/source/generate.py`; all
coverage, subgroup membership, and word evaluations are kernel checked.

Source: Aschbacher, *Sporadic Groups* (1994), §20, pp.96–99, §38,
Exercise 13.2(1), p.210, and §41, pp.219–222.
-/

section
noncomputable section
open scoped Pointwise
open Sporadic.Mathieu
namespace Sporadic.Mathieu.M24LocalGeometry.OctadGraph
open PairOvergroups Theory.GroupTheory.GraphUniquenessSystem
namespace LocalWords
open PairOvergroups.QuotientConstruction.AffineLiftConstruction
open M24ValueBoundParabolics.Construction

def generator : Fin 9 → M24 :=
  ![(MulAut.conj SextetCore.transport) (SylowNormalizer.generator 0),
    (MulAut.conj SextetCore.transport) (SylowNormalizer.generator 1),
    (MulAut.conj SextetCore.transport) (SylowNormalizer.generator 2),
    (MulAut.conj SextetCore.transport) (SylowNormalizer.generator 3),
    (MulAut.conj SextetCore.transport) (extra 0),
    (generatorLift 0).val, (generatorLift 1).val,
    (generatorLift 2).val, (generatorLift 3).val]

def point : Fin 9 → Fin 24 → Fin 24 :=
  ![![10, 16, 23, 22, 14, 6, 17, 21, 12, 4, 1, 9, 8, 20, 11, 18, 0, 19, 15, 5, 13, 7, 2, 3],
    ![10, 23, 16, 22, 7, 15, 6, 4, 8, 9, 0, 20, 17, 13, 14, 5, 2, 12, 18, 19, 11, 21, 3, 1],
    ![1, 0, 3, 2, 5, 4, 6, 7, 21, 9, 22, 17, 12, 18, 14, 15, 23, 11, 13, 19, 20, 8, 10, 16],
    ![0, 2, 1, 3, 7, 12, 19, 4, 8, 9, 10, 20, 5, 21, 14, 17, 23, 15, 18, 6, 11, 13, 22, 16],
    ![1, 2, 0, 3, 13, 18, 6, 11, 15, 9, 10, 21, 5, 20, 14, 17, 22, 8, 12, 19, 4, 7, 23, 16],
    ![7, 15, 20, 12, 4, 5, 22, 0, 8, 10, 9, 11, 3, 13, 23, 1, 19, 17, 18, 16, 2, 21, 6, 14],
    ![7, 15, 20, 12, 0, 1, 21, 4, 10, 8, 9, 2, 17, 16, 18, 5, 19, 3, 23, 13, 11, 22, 6, 14],
    ![0, 2, 3, 1, 4, 11, 14, 7, 8, 9, 10, 17, 15, 21, 19, 20, 22, 5, 13, 6, 12, 18, 23, 16],
    ![0, 1, 22, 10, 18, 13, 20, 7, 21, 12, 3, 17, 9, 5, 14, 15, 16, 11, 4, 19, 6, 8, 2, 23]]

theorem generator_apply (i : Fin 9) (x : Fin 24) :
    (generator i).val x = point i x := by
  fin_cases i <;> revert x <;> decide +kernel

def evaluate : List (Fin 9) → M24
  | [] => 1
  | a :: w => generator a * evaluate w

def evaluatePoint : List (Fin 9) → Fin 24 → Fin 24
  | [], x => x
  | a :: w, x => point a (evaluatePoint w x)

theorem evaluate_apply (w : List (Fin 9)) (x : Fin 24) :
    (evaluate w).val x = evaluatePoint w x := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change (generator a).val ((evaluate w).val x) = _
    rw [generator_apply, ih]
    rfl

theorem evaluate_smul (w : List (Fin 9)) (A : Finset (Fin 24)) :
    evaluate w • A = A.image (evaluatePoint w) := by
  change A.image (evaluate w).val = _
  exact Finset.image_congr (fun x _ => evaluate_apply w x)

def neighborWord : Fin 30 → List (Fin 9) :=
  ![[],
    [0],
    [1],
    [1, 0],
    [4, 1],
    [8, 1],
    [4, 1, 0],
    [8, 1, 0],
    [8, 4, 1],
    [0, 8, 1],
    [3, 8, 1],
    [7, 8, 1],
    [8, 4, 1, 0],
    [0, 8, 1, 0],
    [3, 8, 1, 0],
    [7, 8, 1, 0],
    [0, 8, 4, 1],
    [1, 8, 4, 1],
    [4, 8, 4, 1],
    [7, 8, 4, 1],
    [0, 0, 8, 1],
    [2, 0, 8, 1],
    [3, 0, 8, 1],
    [2, 3, 8, 1],
    [0, 7, 8, 1],
    [7, 8, 4, 1, 0],
    [2, 3, 8, 1, 0],
    [0, 7, 8, 1, 0],
    [7, 4, 8, 4, 1],
    [0, 7, 8, 4, 1]]

def planeWord : Fin 15 → List (Fin 9) :=
  ![[],
    [5],
    [0, 5],
    [1, 5],
    [1, 0, 5],
    [4, 1, 5],
    [5, 1, 5],
    [4, 1, 0, 5],
    [5, 1, 0, 5],
    [5, 4, 1, 5],
    [0, 5, 1, 5],
    [1, 5, 1, 5],
    [3, 5, 1, 5],
    [5, 4, 1, 0, 5],
    [1, 0, 5, 1, 5]]

def edgeWord : Fin 90 → List (Fin 9) :=
  ![[],
    [0],
    [1],
    [5],
    [1, 0],
    [5, 0],
    [4, 1],
    [5, 1],
    [0, 5],
    [1, 5],
    [4, 1, 0],
    [5, 1, 0],
    [0, 5, 0],
    [1, 5, 0],
    [5, 4, 1],
    [0, 5, 1],
    [1, 5, 1],
    [3, 5, 1],
    [4, 5, 1],
    [1, 0, 5],
    [4, 1, 5],
    [5, 1, 5],
    [5, 4, 1, 0],
    [0, 5, 1, 0],
    [3, 5, 1, 0],
    [1, 0, 5, 0],
    [4, 1, 5, 0],
    [5, 1, 5, 0],
    [0, 5, 4, 1],
    [1, 0, 5, 1],
    [3, 0, 5, 1],
    [4, 1, 5, 1],
    [5, 1, 5, 1],
    [4, 3, 5, 1],
    [5, 3, 5, 1],
    [4, 4, 5, 1],
    [5, 4, 5, 1],
    [4, 1, 0, 5],
    [5, 1, 0, 5],
    [5, 4, 1, 5],
    [0, 5, 1, 5],
    [1, 5, 1, 5],
    [3, 5, 1, 5],
    [4, 5, 1, 5],
    [0, 5, 4, 1, 0],
    [1, 0, 5, 1, 0],
    [3, 0, 5, 1, 0],
    [4, 3, 5, 1, 0],
    [5, 3, 5, 1, 0],
    [4, 1, 0, 5, 0],
    [5, 1, 0, 5, 0],
    [5, 4, 1, 5, 0],
    [0, 5, 1, 5, 0],
    [1, 5, 1, 5, 0],
    [3, 5, 1, 5, 0],
    [4, 5, 1, 5, 0],
    [4, 1, 0, 5, 1],
    [5, 1, 0, 5, 1],
    [4, 3, 0, 5, 1],
    [5, 3, 0, 5, 1],
    [5, 4, 1, 5, 1],
    [0, 5, 1, 5, 1],
    [1, 5, 1, 5, 1],
    [3, 5, 1, 5, 1],
    [0, 5, 3, 5, 1],
    [1, 5, 3, 5, 1],
    [3, 5, 3, 5, 1],
    [4, 5, 3, 5, 1],
    [0, 4, 4, 5, 1],
    [0, 5, 4, 5, 1],
    [1, 5, 4, 5, 1],
    [3, 5, 4, 5, 1],
    [5, 4, 1, 0, 5],
    [0, 5, 1, 0, 5],
    [3, 5, 1, 0, 5],
    [0, 5, 4, 1, 5],
    [1, 0, 5, 1, 5],
    [3, 0, 5, 1, 5],
    [4, 1, 5, 1, 5],
    [5, 1, 0, 5, 1, 0],
    [4, 3, 0, 5, 1, 0],
    [5, 4, 1, 0, 5, 0],
    [1, 0, 5, 1, 5, 0],
    [4, 1, 5, 1, 5, 0],
    [5, 4, 1, 0, 5, 1],
    [1, 0, 5, 1, 5, 1],
    [1, 0, 5, 3, 5, 1],
    [5, 0, 4, 4, 5, 1],
    [1, 0, 5, 4, 5, 1],
    [0, 5, 4, 1, 0, 5]]

def neighborIndex : Nat → Fin 30
  | 1626816 => 0
  | 2500912 => 1
  | 674416 => 2
  | 3453312 => 3
  | 2908992 => 4
  | 1996800 => 5
  | 1218736 => 6
  | 2130928 => 7
  | 3690800 => 8
  | 1616672 => 9
  | 3459168 => 10
  | 2797664 => 11
  | 436928 => 12
  | 2511056 => 13
  | 668560 => 14
  | 1330064 => 15
  | 31200 => 16
  | 2804096 => 17
  | 843952 => 18
  | 825680 => 19
  | 1323632 => 20
  | 4096528 => 21
  | 3283776 => 22
  | 1237328 => 23
  | 1966560 => 24
  | 3302048 => 25
  | 2890400 => 26
  | 2161168 => 27
  | 3680464 => 28
  | 447264 => 29
  | _ => 0

def planeIndex : Fin 6 → Fin 6 → Fin 15 :=
  ![![0, 0, 11, 10, 13, 8],
    ![0, 0, 12, 14, 6, 9],
    ![11, 12, 0, 1, 7, 4],
    ![10, 14, 1, 0, 3, 5],
    ![13, 6, 7, 3, 0, 2],
    ![8, 9, 4, 5, 2, 0]]

def edgeIndex : Nat → Fin 90
  | 51 => 0
  | 65 => 1
  | 58 => 2
  | 541 => 3
  | 53 => 4
  | 569 => 5
  | 59 => 6
  | 550 => 7
  | 1045 => 8
  | 793 => 9
  | 52 => 10
  | 545 => 11
  | 1059 => 12
  | 809 => 13
  | 551 => 14
  | 1047 => 15
  | 794 => 16
  | 800 => 17
  | 803 => 18
  | 613 => 19
  | 829 => 20
  | 375 => 21
  | 544 => 22
  | 1052 => 23
  | 797 => 24
  | 634 => 25
  | 844 => 26
  | 365 => 27
  | 1046 => 28
  | 621 => 29
  | 615 => 30
  | 832 => 31
  | 362 => 32
  | 838 => 33
  | 363 => 34
  | 836 => 35
  | 383 => 36
  | 577 => 37
  | 195 => 38
  | 411 => 39
  | 137 => 40
  | 94 => 41
  | 310 => 42
  | 418 => 43
  | 1053 => 44
  | 616 => 45
  | 622 => 46
  | 830 => 47
  | 377 => 48
  | 599 => 49
  | 190 => 50
  | 400 => 51
  | 116 => 52
  | 83 => 53
  | 293 => 54
  | 398 => 55
  | 585 => 56
  | 189 => 57
  | 579 => 58
  | 188 => 59
  | 412 => 60
  | 119 => 61
  | 82 => 62
  | 292 => 63
  | 118 => 64
  | 81 => 65
  | 291 => 66
  | 399 => 67
  | 581 => 68
  | 124 => 69
  | 95 => 70
  | 311 => 71
  | 159 => 72
  | 317 => 73
  | 202 => 74
  | 101 => 75
  | 341 => 76
  | 125 => 77
  | 167 => 78
  | 196 => 79
  | 587 => 80
  | 155 => 81
  | 328 => 82
  | 152 => 83
  | 153 => 84
  | 329 => 85
  | 326 => 86
  | 161 => 87
  | 340 => 88
  | 353 => 89
  | _ => 0

def edgeIndexOf (i j a b : Fin 6) : Fin 90 :=
  edgeIndex ((min i.val j.val * 6 + max i.val j.val) * 36 +
    min a.val b.val * 6 + max a.val b.val)

theorem neighbor_coverage : ∀ b : Fin 759,
    Disjoint (standardTrioOctad 0) (m24BlockAt b) →
      (standardTrioOctad 1).image
        (evaluatePoint (neighborWord (neighborIndex (m24BlockMaskValue b)))) = m24BlockAt b := by
  decide +kernel

theorem plane_coverage : ∀ i j : Fin 6, i ≠ j →
    (standardTrioOctad 0).image (evaluatePoint (planeWord (planeIndex i j))) =
      standardTetrad i ∪ standardTetrad j := by
  decide +kernel

theorem edge_coverage : ∀ i j a b : Fin 6,
    i ≠ j → a ≠ b → i ≠ a → i ≠ b → j ≠ a → j ≠ b →
      (standardTrioOctad 0).image (evaluatePoint (edgeWord (edgeIndexOf i j a b))) =
        standardTetrad i ∪ standardTetrad j ∧
      (standardTrioOctad 1).image (evaluatePoint (edgeWord (edgeIndexOf i j a b))) =
        standardTetrad a ∪ standardTetrad b := by
  decide +kernel


def vertexJoin : Subgroup M24 :=
  edgeFixer M24 first second ⊔
    (sextetStabilizer standardSextet ⊓ MulAction.stabilizer M24 first)

def localJoin : Subgroup M24 :=
  (sextetStabilizer standardSextet ⊓ edgeStabilizer M24 first second) ⊔
    (sextetStabilizer standardSextet ⊓ MulAction.stabilizer M24 first)

theorem generator_smul (i : Fin 9) (A : Finset (Fin 24)) :
    generator i • A = A.image (point i) := by
  change A.image (generator i).val = _
  exact Finset.image_congr (fun x _ => generator_apply i x)

theorem generator_first (i : Fin 9) (hi : i.val < 5 ∨ 7 ≤ i.val) :
    generator i • first = first := by
  apply Subtype.ext
  change generator i • first.val = first.val
  rw [generator_smul]
  exact (by decide +kernel : ∀ i : Fin 9, i.val < 5 ∨ 7 ≤ i.val →
    first.val.image (point i) = first.val) i hi

theorem generator_second (i : Fin 9) (hi : 7 ≤ i.val) :
    generator i • second = second := by
  apply Subtype.ext
  change generator i • second.val = second.val
  rw [generator_smul]
  exact (by decide +kernel : ∀ i : Fin 9, 7 ≤ i.val →
    second.val.image (point i) = second.val) i hi

theorem generator_sextet (i : Fin 9) (hi : i.val < 6) :
    generator i ∈ sextetStabilizer standardSextet := by
  change standardSextet.parts.image (fun A => generator i • A) = standardSextet.parts
  simp only [generator_smul]
  exact (by decide +kernel : ∀ i : Fin 9, i.val < 6 →
    standardSextet.parts.image (fun A => A.image (point i)) = standardSextet.parts) i hi

theorem generator_swap : generator 5 • first = second ∧ generator 5 • second = first := by
  constructor <;> apply Subtype.ext
  · change generator 5 • first.val = second.val
    rw [generator_smul]
    decide +kernel
  · change generator 5 • second.val = first.val
    rw [generator_smul]
    decide +kernel

theorem generator_vertexJoin (i : Fin 9) (hi : i.val < 5 ∨ 7 ≤ i.val) :
    generator i ∈ vertexJoin := by
  rcases hi with hi | hi
  · exact Subgroup.mem_sup_right ⟨generator_sextet i (by omega), generator_first i (Or.inl hi)⟩
  · exact Subgroup.mem_sup_left ⟨generator_first i (Or.inr hi), generator_second i hi⟩

theorem generator_localJoin (i : Fin 9) (hi : i.val < 6) :
    generator i ∈ localJoin := by
  by_cases h : i.val < 5
  · exact Subgroup.mem_sup_right ⟨generator_sextet i hi, generator_first i (Or.inl h)⟩
  · have he : i = 5 := Fin.ext (by omega)
    subst i
    exact Subgroup.mem_sup_left ⟨generator_sextet 5 (by decide), Or.inr generator_swap⟩

theorem evaluate_mem (K : Subgroup M24) (w : List (Fin 9))
    (hw : ∀ i ∈ w, generator i ∈ K) : evaluate w ∈ K := by
  induction w with
  | nil => exact K.one_mem
  | cons i w ih => exact K.mul_mem (hw i (by simp)) (ih (fun j hj => hw j (by simp [hj])))

theorem neighborWord_mem (i : Fin 30) : evaluate (neighborWord i) ∈ vertexJoin := by
  apply evaluate_mem
  intro j hj
  apply generator_vertexJoin
  exact (by decide +kernel : ∀ i : Fin 30, ∀ j ∈ neighborWord i,
    j.val < 5 ∨ 7 ≤ j.val) i j hj

theorem planeWord_mem (i : Fin 15) : evaluate (planeWord i) ∈ localJoin := by
  apply evaluate_mem
  intro j hj
  apply generator_localJoin
  exact (by decide +kernel : ∀ i : Fin 15, ∀ j ∈ planeWord i, j.val < 6) i j hj

theorem edgeWord_mem (i : Fin 90) : evaluate (edgeWord i) ∈ sextetStabilizer standardSextet := by
  apply evaluate_mem
  intro j hj
  apply generator_sextet
  exact (by decide +kernel : ∀ i : Fin 90, ∀ j ∈ edgeWord i, j.val < 6) i j hj

theorem vertexJoin_le : vertexJoin ≤ MulAction.stabilizer M24 first :=
  sup_le inf_le_left inf_le_right

theorem localJoin_le : localJoin ≤ sextetStabilizer standardSextet :=
  sup_le inf_le_left inf_le_left

theorem neighbor_transitive (O : Octad) (hO : graph.Adj first O) :
    ∃ g ∈ vertexJoin, g • second = O := by
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp O.property
  refine ⟨evaluate (neighborWord (neighborIndex (m24BlockMaskValue b))), neighborWord_mem _, ?_⟩
  apply Subtype.ext
  change evaluate _ • second.val = O.val
  rw [evaluate_smul]
  exact (neighbor_coverage b (by rw [hb]; exact hO)).trans hb

theorem plane_transitive (O : Octad) (hO : OnPlane O standardSextet) :
    ∃ g ∈ localJoin, g • first = O := by
  obtain ⟨A,hA,B,hB,hne,he⟩ := hO
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
  have hij : i ≠ j := fun h => hne (congrArg standardTetrad h)
  refine ⟨evaluate (planeWord (planeIndex i j)), planeWord_mem _, ?_⟩
  apply Subtype.ext
  change evaluate _ • first.val = O.val
  rw [evaluate_smul]
  exact (plane_coverage i j hij).trans he.symm

theorem plane_edge_transitive {O P : Octad} (hOP : graph.Adj O P)
    (hO : OnPlane O standardSextet) (hP : OnPlane P standardSextet) :
    ∃ g ∈ sextetStabilizer standardSextet, g • first = O ∧ g • second = P := by
  obtain ⟨A,hA,B,hB,hAB,heO⟩ := hO
  obtain ⟨C,hC,D,hD,hCD,heP⟩ := hP
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hD
  have hdis : Disjoint (standardTetrad i ∪ standardTetrad j)
      (standardTetrad a ∪ standardTetrad b) := by
    rw [← heO, ← heP]; exact hOP
  have cross (k l : Fin 6) (hk : standardTetrad k ⊆ standardTetrad i ∪ standardTetrad j)
      (hl : standardTetrad l ⊆ standardTetrad a ∪ standardTetrad b) : k ≠ l := by
    rintro rfl
    have hempty : standardTetrad k = ∅ := disjoint_self.mp (hdis.mono hk hl)
    have hc := standardTetrad_card k
    rw [hempty, Finset.card_empty] at hc
    omega
  have hi : i ≠ j := fun h => hAB (congrArg standardTetrad h)
  have ha : a ≠ b := fun h => hCD (congrArg standardTetrad h)
  obtain ⟨h1,h2⟩ := edge_coverage i j a b hi ha
    (cross i a Finset.subset_union_left Finset.subset_union_left)
    (cross i b Finset.subset_union_left Finset.subset_union_right)
    (cross j a Finset.subset_union_right Finset.subset_union_left)
    (cross j b Finset.subset_union_right Finset.subset_union_right)
  refine ⟨evaluate (edgeWord (edgeIndexOf i j a b)), edgeWord_mem _, ?_, ?_⟩
  · apply Subtype.ext
    change evaluate _ • first.val = O.val
    rw [evaluate_smul]
    exact h1.trans heO.symm
  · apply Subtype.ext
    change evaluate _ • second.val = P.val
    rw [evaluate_smul]
    exact h2.trans heP.symm

end LocalWords

/-- The actual pointwise edge fixer and plane–point stabilizer generate the
whole octad stabilizer. The proof covers its thirty neighbors by words in
these subgroups, then uses the literal point stabilizer. -/
public theorem vertex_generate :
    edgeFixer M24 first second ⊔
      (sextetStabilizer standardSextet ⊓ MulAction.stabilizer M24 first) =
        MulAction.stabilizer M24 first := by
  apply le_antisymm LocalWords.vertexJoin_le
  intro g hg
  have hO : graph.Adj first (g • second) := by
    simpa only [show g • first = first from hg] using preserves g first_adj_second
  obtain ⟨k,hk,he⟩ := LocalWords.neighbor_transitive (g • second) hO
  have hkg : k⁻¹ * g ∈ edgeFixer M24 first second := by
    constructor
    · change (k⁻¹ * g) • first = first
      rw [mul_smul, show g • first = first from hg, inv_smul_eq_iff]
      exact (LocalWords.vertexJoin_le hk).symm
    · change (k⁻¹ * g) • second = second
      rw [mul_smul, inv_smul_eq_iff]
      exact he.symm
  have hm := LocalWords.vertexJoin.mul_mem hk (Subgroup.mem_sup_left hkg)
  simpa only [mul_inv_cancel_left] using hm

/-- The actual plane edge and plane–point stabilizers generate the full
sextet stabilizer, by its transitive action on the fifteen incident octads. -/
public theorem local_generate :
    (sextetStabilizer standardSextet ⊓ edgeStabilizer M24 first second) ⊔
      (sextetStabilizer standardSextet ⊓ MulAction.stabilizer M24 first) =
        sextetStabilizer standardSextet := by
  apply le_antisymm LocalWords.localJoin_le
  intro g hg
  have hO : OnPlane (g • first) standardSextet := by
    have he : g • standardSextet = standardSextet := by
      apply Sextet.ext
      exact hg
    simpa only [he] using onPlane_smul g
      (standardTrio_on_standardSextet first first_on_standardTrio)
  obtain ⟨k,hk,he⟩ := LocalWords.plane_transitive (g • first) hO
  have hkg : k⁻¹ * g ∈ sextetStabilizer standardSextet ⊓ MulAction.stabilizer M24 first := by
    refine ⟨(sextetStabilizer standardSextet).mul_mem
      ((sextetStabilizer standardSextet).inv_mem (LocalWords.localJoin_le hk)) hg, ?_⟩
    change (k⁻¹ * g) • first = first
    rw [mul_smul, inv_smul_eq_iff]
    exact he.symm
  have hm := LocalWords.localJoin.mul_mem hk (Subgroup.mem_sup_right hkg)
  simpa only [mul_inv_cancel_left] using hm

/-- Every directed edge in the marked sextet is in its literal stabilizer orbit. -/
public theorem plane_edge_transitive {O P : Octad} (hOP : graph.Adj O P)
    (hO : OnPlane O standardSextet) (hP : OnPlane P standardSextet) :
    ∃ g : sextetStabilizer standardSextet, (g : M24) • first = O ∧ (g : M24) • second = P := by
  obtain ⟨g,hg,h1,h2⟩ := LocalWords.plane_edge_transitive hOP hO hP
  exact ⟨⟨g,hg⟩,h1,h2⟩

/-- The marked native edge can be reversed inside its actual sextet stabilizer. -/
public theorem exists_local_swap : ∃ g : sextetStabilizer standardSextet,
    (g : M24) • first = second ∧ (g : M24) • second = first :=
  plane_edge_transitive first_adj_second.symm
    (standardTrio_on_standardSextet second second_on_standardTrio)
    (standardTrio_on_standardSextet first first_on_standardTrio)

end Sporadic.Mathieu.M24LocalGeometry.OctadGraph
