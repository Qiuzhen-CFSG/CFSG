module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/Primitivity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, public module boundaries, and Lean 4.33 proof adaptation.
-/

public import Theory.AtlasPort.LinearGroups.G2.OrbitClasses
public import Theory.AtlasPort.LinearGroups.G2.PlaneBlock
public import Theory.AtlasPort.LinearGroups.G2.BlockArithmetic
public import Theory.AtlasPort.GroupTheory.G2FiniteSuborbitBlocks

/-! Suborbit decomposition and block-size divisibility reduce primitivity to excluding the distinguished plane, including over the binary field. -/

@[expose] public section

noncomputable section
namespace Atlas.G2
variable {K : Type*} [Field K] [Finite K]

theorem card_orbitClass (i : Fin 4) :
    Nat.card {p : SingularPoints K // orbitClass p = i} = singularSubdegree (Nat.card K) i := by
  fin_cases i
  · exact card_orbitClass_zero
  · exact card_orbitClass_one
  · exact card_orbitClass_two
  · exact card_orbitClass_three

theorem singularPoints_primitive : MulAction.IsPreprimitive (Model K) (SingularPoints K) := by
  classical
  apply MulAction.IsPreprimitive.of_isTrivialBlock_base firstPoint
  intro B ha hB
  have htrans (p q : SingularPoints K) (h : orbitClass p = orbitClass q) :
      ∃ g : pointStabilizer (K := K), g • p = q := by
    obtain ⟨g,hg⟩ := (orbitClass_eq_iff p q).mp h
    exact ⟨⟨g.val,parabolic_le_pointStabilizer g.property⟩,hg⟩
  obtain ⟨T,hT,hBset,hBcard⟩ := Atlas.GroupTheory.block_suborbit_decomposition
    firstPoint orbitClass htrans (singularSubdegree (Nat.card K)) card_orbitClass B ha hB
  have hzero : (0 : Fin 4) ∈ T := by
    simpa only [(orbitClass_zero_iff firstPoint).mpr rfl] using hT
  have hdegree : Nat.card (SingularPoints K) =
      Nat.card K^5+Nat.card K^4+Nat.card K^3+Nat.card K^2+Nat.card K+1 := by
    rw [card_singularPoints_sum]
    simp [Finset.sum_range_succ]
    ring
  have hdiv : (∑ i ∈ T, singularSubdegree (Nat.card K) i) ∣
      Nat.card K^5+Nat.card K^4+Nat.card K^3+Nat.card K^2+Nat.card K+1 := by
    rw [← hBcard,← hdegree]
    exact hB.ncard_dvd_card ⟨firstPoint,ha⟩
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card (α := K)
  rcases subdegree_block_index_candidates (Nat.card K) hq T hzero hdiv with h|h|h
  · left
    rw [h] at hBset
    intro p hp q hq
    have hp0 : orbitClass p=0 := by simpa [hBset] using hp
    have hq0 : orbitClass q=0 := by simpa [hBset] using hq
    exact ((orbitClass_zero_iff p).mp hp0).trans ((orbitClass_zero_iff q).mp hq0).symm
  · exfalso
    have he : B=planePoints := by
      rw [hBset,h]
      ext p
      change orbitClass p ∈ ({0,1} : Finset (Fin 4)) ↔ p ∈ planePoints
      rw [mem_planePoints_iff,← orbitClass_le_one_iff]
      simp only [Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro (he|he) <;> simp [he]
      · intro he
        have hv := (orbitClass p).isLt
        rcases (show (orbitClass p).val=0 ∨ (orbitClass p).val=1 by omega) with hv|hv
        · exact Or.inl (Fin.ext hv)
        · exact Or.inr (Fin.ext hv)
    exact planePoints_not_block (he ▸ hB)
  · right
    rw [hBset,h]
    simp

end Atlas.G2
