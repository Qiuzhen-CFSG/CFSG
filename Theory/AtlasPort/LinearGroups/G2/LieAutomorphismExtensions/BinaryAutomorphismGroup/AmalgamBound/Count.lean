module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.Candidates
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The 64-element bound for the binary amalgam sieve

The order and relator conditions restrict the two local generator images to
32 left pairs and 64 right pairs. Among pairs with the same common-generator
image, agreement at overlap row 2 already gives a cover by 64 signatures.
Every `Candidate` satisfies these necessary conditions, so its inclusion into
that cover gives the bound. No presentation-completeness or global-automorphism
claim enters the argument; the full published `Compatible` predicate is retained.

The lists can be reconstructed using `candidates` in `source/generate.py` in
the parent directory. All coverage assertions below are checked by Lean's
kernel. The diagnostic generation is not used as a proof.

Root coordinate attribution: Gerald Höhn and the ATLAS contributors, ATLAS
Research and Attribution License 1.0 (`LICENSES/ATLAS.txt`); see `Data`.
Source application: Aschbacher--Smith F.1.12 and Definition F.4.3. This supplies
the count premise of `card_binaryAmalgamAut_le_of_word_certificate`; the actual
group realization is a separate premise of that theorem.
-/

@[expose] public section
namespace Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound

private def relatorCandidate (T : WordTable) (x y : Fin 96) : Prop :=
  T.eval x y [false, false, false, false] ≠ 0 ∧ y ≠ 0 ∧
    ∀ w ∈ T.relations, T.eval x y w = 0

private instance (T : WordTable) (x y : Fin 96) : Decidable (relatorCandidate T x y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀ w ∈ T.relations, _))

private def leftImages (k : Fin 32) : List (Fin 96) :=
  match k.val with
  | 1 => [2, 6, 61, 90]
  | 8 => [2, 6, 61, 90]
  | 11 => [2, 6, 61, 90]
  | 14 => [59, 60, 62, 63]
  | 18 => [59, 60, 62, 63]
  | 24 => [59, 60, 62, 63]
  | 27 => [59, 60, 62, 63]
  | 31 => [2, 6, 61, 90]
  | _ => []

private theorem left_relator_coverage : ∀ (k : Fin 32) (y : Fin 96),
    relatorCandidate leftTable (leftTable.overlap k) y →
    y ∈ leftImages k := by
  decide +kernel

private def rightImages (k : Fin 32) : List (Fin 96) :=
  match k.val with
  | 1 => [2, 42, 53, 64, 80, 84, 86, 90]
  | 8 => [22, 48, 51, 56, 60, 66, 69, 73]
  | 11 => [17, 20, 25, 28, 29, 31, 34, 37]
  | 14 => [8, 11, 22, 48, 56, 66, 77, 82]
  | 18 => [20, 28, 31, 37, 53, 64, 86, 90]
  | 24 => [6, 9, 51, 60, 69, 73, 85, 91]
  | 27 => [2, 17, 25, 29, 34, 42, 80, 84]
  | 31 => [6, 8, 9, 11, 77, 82, 85, 91]
  | _ => []

private theorem right_relator_coverage : ∀ (k : Fin 32) (y : Fin 96),
    relatorCandidate rightTable (rightTable.overlap k) y →
    y ∈ rightImages k := by
  decide +kernel

private def signatureCover : List Signature :=
  [
    (1, 2, 2), (1, 2, 42), (1, 2, 80), (1, 2, 84),
    (1, 90, 53), (1, 90, 64), (1, 90, 86), (1, 90, 90),
    (8, 2, 22), (8, 2, 48), (8, 2, 56), (8, 2, 66),
    (8, 90, 51), (8, 90, 60), (8, 90, 69), (8, 90, 73),
    (11, 6, 17), (11, 6, 25), (11, 6, 29), (11, 6, 34),
    (11, 61, 20), (11, 61, 28), (11, 61, 31), (11, 61, 37),
    (14, 62, 8), (14, 62, 11), (14, 62, 77), (14, 62, 82),
    (14, 63, 22), (14, 63, 48), (14, 63, 56), (14, 63, 66),
    (18, 59, 20), (18, 59, 28), (18, 59, 31), (18, 59, 37),
    (18, 60, 53), (18, 60, 64), (18, 60, 86), (18, 60, 90),
    (24, 59, 6), (24, 59, 9), (24, 59, 85), (24, 59, 91),
    (24, 60, 51), (24, 60, 60), (24, 60, 69), (24, 60, 73),
    (27, 62, 17), (27, 62, 25), (27, 62, 29), (27, 62, 34),
    (27, 63, 2), (27, 63, 42), (27, 63, 80), (27, 63, 84),
    (31, 6, 8), (31, 6, 11), (31, 6, 77), (31, 6, 82),
    (31, 61, 6), (31, 61, 9), (31, 61, 85), (31, 61, 91)
  ]

private theorem compatibility_coverage : ∀ k : Fin 32,
    ∀ y ∈ leftImages k, ∀ z ∈ rightImages k,
    leftTable.label (leftTable.eval (leftTable.overlap k) y
      (leftTable.word (leftTable.overlap 2))) =
    rightTable.label (rightTable.eval (rightTable.overlap k) z
      (rightTable.word (rightTable.overlap 2))) →
    (k, y, z) ∈ signatureCover := by
  decide +kernel

private theorem candidate_mem_cover (s : Candidate) : s.val ∈ signatureCover := by
  have h := s.property
  exact compatibility_coverage s.val.1 s.val.2.1
    (left_relator_coverage _ _ ⟨h.1.1, h.1.2.1, h.1.2.2.1⟩) s.val.2.2
    (right_relator_coverage _ _ ⟨h.2.1.1, h.2.1.2.1, h.2.1.2.2.1⟩) (h.2.2 2)

/-- The exact published finite candidate predicate has at most 64 solutions. -/
theorem card_candidate_le : Nat.card Candidate ≤ 64 := by
  let f : Candidate → ↥signatureCover.toFinset :=
    fun s => ⟨s.val, List.mem_toFinset.mpr (candidate_mem_cover s)⟩
  have hf : Function.Injective f := by
    intro s t h
    exact Subtype.ext (congrArg (fun x : ↥signatureCover.toFinset => x.val) h)
  calc
    Nat.card Candidate ≤ Nat.card ↥signatureCover.toFinset :=
      Nat.card_le_card_of_injective f hf
    _ = signatureCover.toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ signatureCover.length := List.toFinset_card_le _
    _ = 64 := rfl

end Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound
