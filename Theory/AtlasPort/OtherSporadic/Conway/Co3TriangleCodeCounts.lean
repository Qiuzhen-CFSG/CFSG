/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3TriangleCodeCounts.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadIncidenceCounts
public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleShapes
/-!
Intrinsic 2-3-4 Leech triangles and their Conway stabilizer action.
The proofs use concrete Golay coordinate parameters, incidence counts, and orbit transport.

Source: Gerald Höhn, `Atlas/Conway/Co3TriangleCodeCounts.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

abbrev GolayCoordinateWeight (k : ℕ) (a : Omega) (v : Bit) :=
  {c : golay // hammingNorm c.val = k ∧ c.val a = v}

theorem golay_coordinate_support (c : golay) (a : Omega) :
    a ∈ support c.val ↔ c.val a = 1 := by
  rcases bit_cases (c.val a) with h | h <;> simp [support,h]

def golayWeightSupportEquiv (k : ℕ) (B : Finset (Finset Omega))
    (hB : ∀ T, T ∈ B ↔ ∃ c : golay, hammingNorm c.val = k ∧ support c.val = T)
    (P : Finset Omega → Prop) :
    {c : golay // hammingNorm c.val = k ∧ P (support c.val)} ≃
      {T // T ∈ B.filter P} :=
  Equiv.ofBijective (fun c => ⟨support c.val.val,
    Finset.mem_filter.mpr ⟨(hB _).mpr ⟨c.val,c.prop.1,rfl⟩,c.prop.2⟩⟩) ⟨by
      intro c d h
      apply Subtype.ext
      apply Subtype.ext
      exact binarySupportEquiv.injective (congrArg Subtype.val h),by
      intro T
      obtain ⟨hT,hP⟩ := Finset.mem_filter.mp T.prop
      obtain ⟨c,hc,hs⟩ := (hB T.val).mp hT
      exact ⟨⟨c,hc,hs ▸ hP⟩,Subtype.ext hs⟩⟩

theorem golay_coordinate_one_card (k : ℕ) (B : Finset (Finset Omega))
    (hB : ∀ T, T ∈ B ↔ ∃ c : golay, hammingNorm c.val = k ∧ support c.val = T)
    (a : Omega) : Nat.card (GolayCoordinateWeight k a 1) = (B.filter (fun T => a ∈ T)).card := by
  let e := Equiv.subtypeEquivRight (fun c : golay =>
    and_congr_right (fun (_ : hammingNorm c.val = k) => (golay_coordinate_support c a).symm))
  rw [Nat.card_congr e,Nat.card_congr (golayWeightSupportEquiv k B hB (fun T => a ∈ T)),
    Nat.card_eq_fintype_card,Fintype.card_coe]
  congr 1
  ext T
  simp

theorem golay_coordinate_zero_card (k : ℕ) (B : Finset (Finset Omega))
    (hB : ∀ T, T ∈ B ↔ ∃ c : golay, hammingNorm c.val = k ∧ support c.val = T)
    (a : Omega) : Nat.card (GolayCoordinateWeight k a 0) = (B.filter (fun T => a ∉ T)).card := by
  let e := Equiv.subtypeEquivRight (fun c : golay =>
    and_congr_right (fun (_ : hammingNorm c.val = k) => show c.val a = 0 ↔ a ∉ support c.val by simp [support]))
  rw [Nat.card_congr e,Nat.card_congr (golayWeightSupportEquiv k B hB (fun T => a ∉ T)),
    Nat.card_eq_fintype_card,Fintype.card_coe]
  congr 1
  ext T
  simp

theorem golay_octad_coordinate_one_card (a : Omega) : Nat.card (GolayCoordinateWeight 8 a 1) = 253 := by
  rw [golay_coordinate_one_card 8 octads octads_mem,octads_through_point_card]

theorem golay_octad_coordinate_zero_card (a : Omega) : Nat.card (GolayCoordinateWeight 8 a 0) = 506 := by
  rw [golay_coordinate_zero_card 8 octads octads_mem,octads_avoiding_point_card]

theorem golay_dodecad_coordinate_zero_card (a : Omega) : Nat.card (GolayCoordinateWeight 12 a 0) = 1288 := by
  rw [golay_coordinate_zero_card 12 dodecads dodecads_mem,dodecads_avoiding_point_card]

def golayCodeComplement (c : golay) : golay :=
  ⟨c.val+allOnes,golay.add_mem c.prop (C0_le_golay allOnes_mem_C0)⟩

theorem golayCodeComplement_involutive : Function.Involutive golayCodeComplement := by
  intro c
  apply Subtype.ext
  funext i
  change (c.val i+1)+1 = c.val i
  simp [add_assoc]

def golaySixteenCoordinateEquiv (a : Omega) :
    GolayCoordinateWeight 16 a 1 ≃ GolayCoordinateWeight 8 a 0 where
  toFun c := ⟨golayCodeComplement c.val,by
    have h := complement_weight c.val.val
    change hammingNorm (c.val.val+allOnes) = 8 ∧ c.val.val a+1 = 0
    constructor
    · have := c.prop.1; omega
    · rw [c.prop.2]; decide⟩
  invFun c := ⟨golayCodeComplement c.val,by
    have h := complement_weight c.val.val
    change hammingNorm (c.val.val+allOnes) = 16 ∧ c.val.val a+1 = 1
    constructor
    · have := c.prop.1; omega
    · rw [c.prop.2]; simp⟩
  left_inv c := Subtype.ext (golayCodeComplement_involutive c.val)
  right_inv c := Subtype.ext (golayCodeComplement_involutive c.val)

theorem golay_sixteen_coordinate_one_card (a : Omega) :
    Nat.card (GolayCoordinateWeight 16 a 1) = 506 := by
  rw [Nat.card_congr (golaySixteenCoordinateEquiv a),golay_octad_coordinate_zero_card]

end Atlas.Conway
