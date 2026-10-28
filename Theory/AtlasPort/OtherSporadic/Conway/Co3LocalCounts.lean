/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3LocalCounts.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3LocalMathieuOrbits
/-!
The norm-six stabilizer acting on decompositions into minimum Leech vectors.
The proofs connect the concrete coordinate action with Mathieu incidence geometry.

Source: Gerald Höhn, `Atlas/Conway/Co3LocalCounts.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices Atlas.Combinatorics
attribute [local instance] Classical.propDecidable
local instance co3LocalCountPointsFintype (a : Omega) : Fintype (Mathieu23Points a) := Fintype.ofFinite _

theorem co3_heptads_card (a : Omega) : Nat.card (Co3Heptads a) = 253 := by
  rw [Nat.card_eq_fintype_card,Fintype.card_coe,mathieu23Blocks_card]

theorem co3_heptads_through_card (a : Omega) (b : Mathieu23Points a) :
    Nat.card {B : Co3Heptads a // b ∈ B.val} = 77 := by
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun B => B ∈ mathieu23Blocks a) (fun B => b ∈ B)),
    ← Nat.card_congr (derivedBlocksThroughEquiv (mathieu23Blocks a) b),
    Nat.card_eq_fintype_card,Fintype.card_coe]
  exact mathieu22Blocks_card a b

theorem co3_heptads_avoiding_card (a : Omega) (b : Mathieu23Points a) :
    Nat.card {B : Co3Heptads a // b ∉ B.val} = 176 := by
  have h := Fintype.card_subtype_compl (fun B : Co3Heptads a => b ∈ B.val)
  simp only [← Nat.card_eq_fintype_card,co3_heptads_card,co3_heptads_through_card] at h
  exact h

abbrev Co3LocalParameters (a : Omega) (b : Mathieu23Points a) : Fin 4 → Type
  | 0 => PUnit
  | 1 => {c : Mathieu23Points a // c ≠ b}
  | 2 => {B : Co3Heptads a // b ∈ B.val}
  | 3 => {B : Co3Heptads a // b ∉ B.val}

def co3LocalParameterMap (a : Omega) (b : Mathieu23Points a) :
    (t : Fin 4) → Co3LocalParameters a b t → {q : Co3PointHeptad a // co3LocalType a b q = t}
  | 0, _ => ⟨Sum.inl b,by simp [co3LocalType]⟩
  | 1, c => ⟨Sum.inl c.val,by simp [co3LocalType,c.prop]⟩
  | 2, B => ⟨Sum.inr B.val,by simp [co3LocalType,B.prop]⟩
  | 3, B => ⟨Sum.inr B.val,by simp [co3LocalType,B.prop]⟩

def co3LocalParameterEquiv (a : Omega) (b : Mathieu23Points a) (t : Fin 4) :
    Co3LocalParameters a b t ≃ {q : Co3PointHeptad a // co3LocalType a b q = t} :=
  Equiv.ofBijective (co3LocalParameterMap a b t) ⟨by
    intro x y h
    fin_cases t
    · exact Subsingleton.elim _ _
    · exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
    · exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val h))
    · exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val h)),by
    rintro ⟨q,hq⟩
    fin_cases t <;> cases q with
    | inl c =>
      simp only [co3LocalType] at hq
      first
      | (have hc : c = b := by by_contra hn; simp [hn] at hq
         subst c
         exact ⟨PUnit.unit,rfl⟩)
      | (have hc : c ≠ b := by intro hn; simp [hn] at hq
         exact ⟨⟨c,hc⟩,rfl⟩)
      | (split_ifs at hq <;> contradiction)
    | inr B =>
      simp only [co3LocalType] at hq
      first
      | (have hB : b ∈ B.val := by by_contra hn; simp [hn] at hq
         exact ⟨⟨B,hB⟩,rfl⟩)
      | (have hB : b ∉ B.val := by intro hn; simp [hn] at hq
         exact ⟨⟨B,hB⟩,rfl⟩)
      | (split_ifs at hq <;> contradiction)⟩

def co3LocalSize : Fin 4 → ℕ := ![1,22,77,176]

theorem co3LocalType_card (a : Omega) (b : Mathieu23Points a) (t : Fin 4) :
    Nat.card {q : Co3PointHeptad a // co3LocalType a b q = t} = co3LocalSize t := by
  rw [← Nat.card_congr (co3LocalParameterEquiv a b t)]
  fin_cases t
  · simp [Co3LocalParameters,co3LocalSize]
  · change Nat.card {c : Mathieu23Points a // c ≠ b} = 22
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    simp [← Nat.card_eq_fintype_card,mathieu23_degree]
  · exact co3_heptads_through_card a b
  · exact co3_heptads_avoiding_card a b

end Atlas.Conway
