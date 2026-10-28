/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3Simplicity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.Conway3Maximality
public import Theory.AtlasPort.OtherSporadic.Sporadic.Conway3Action
public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu23Simplicity
public import Theory.AtlasPort.OtherSporadic.GroupTheory.NormalSylowIntersection
public import Theory.AtlasPort.OtherSporadic.GroupTheory.NormalSylowEight
/-!
The norm-six stabilizer acting on decompositions into minimum Leech vectors.
The proofs connect the concrete coordinate action with Mathieu incidence geometry.

Source: Gerald Höhn, `Atlas/Conway/Co3Simplicity.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices Atlas.Sporadic.Conway3
open MulAction
local instance co3Prime23 : Fact (Nat.Prime 23) := ⟨by decide⟩

theorem co3_sylow23_card (P : Sylow 23 Model) : Nat.card P = 23 := by
  rw [Sylow.card_eq_multiplicity,card]
  change 23 ^ Nat.factorization 495766656000 23 = 23
  rw [show 495766656000 = 23*21555072000 from rfl,
    Nat.factorization_mul_apply_of_coprime (by decide : Nat.Coprime 23 21555072000),
    (by decide : Nat.Prime 23).factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬23 ∣ 21555072000)]
  norm_num

theorem co3_triangle_stabilizer_simple : IsSimpleGroup TriangleStabilizer := by
  let := mathieu23_simple co3MarkedCoordinate
  exact triangleMathieuEquiv.symm.isSimpleGroup

theorem co3_triangle_stabilizer_not_transitive : ¬ IsPretransitive TriangleStabilizer Points := by
  intro ht
  let := ht
  obtain ⟨B,hB⟩ := Finset.card_pos.mp (show 0 < (mathieu23Blocks co3MarkedCoordinate).card by
    rw [mathieu23Blocks_card]; decide)
  let B' : {B // B ∈ mathieu23Blocks co3MarkedCoordinate} := ⟨B,hB⟩
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq TriangleStabilizer
    (pointHeptadEquiv (Sum.inl co3BasePoint)) (pointHeptadEquiv (Sum.inr B'))
  obtain ⟨p,rfl⟩ := triangleMathieuEquiv.surjective g
  change mathieu23Embedding p • pointHeptadEquiv (Sum.inl co3BasePoint) = pointHeptadEquiv (Sum.inr B') at hg
  rw [← pointHeptad_equivariant] at hg
  have he := pointHeptadEquiv.injective hg
  change Sum.inl (p • co3BasePoint) = Sum.inr B' at he
  cases he

theorem co3_normal_contains_mathieu (N : Subgroup Model) [N.Normal] (hN : N ≠ ⊥) :
    TriangleStabilizer ≤ N := by
  let := faithful
  let := primitive
  let := Atlas.GroupTheory.normal_pretransitive (X := Points) N hN
  have h276 : 276 ∣ Nat.card N := by
    simpa only [degree] using Atlas.GroupTheory.transitive_degree_dvd (G := N) basePoint
  have h23N : 23 ∣ Nat.card N := dvd_trans (by decide : 23 ∣ 276) h276
  have h23M : 23 ∣ Nat.card TriangleStabilizer := by rw [triangle_stabilizer_card]; decide
  obtain ⟨x,hxN,hxM,hx1⟩ := Atlas.GroupTheory.normal_meets_subgroup_of_prime_sylow Model 23
    co3_sylow23_card N TriangleStabilizer h23N h23M
  let := co3_triangle_stabilizer_simple
  have ht : N.comap TriangleStabilizer.subtype = ⊤ := by
    rcases (inferInstance : (N.comap TriangleStabilizer.subtype).Normal).eq_bot_or_eq_top with hb | ht
    · have hx : (⟨x,hxM⟩ : TriangleStabilizer) ∈ N.comap TriangleStabilizer.subtype := hxN
      rw [hb] at hx
      exact False.elim (hx1 (congrArg Subtype.val hx))
    · exact ht
  intro x hx
  have hm : (⟨x,hx⟩ : TriangleStabilizer) ∈ N.comap TriangleStabilizer.subtype := ht ▸ Subgroup.mem_top _
  exact hm

theorem co3_simple : IsSimpleGroup Model := by
  let : Nontrivial Model := by
    obtain ⟨g,h,hne⟩ := exists_mul_ne_mul
    exact ⟨⟨g*h,h*g,hne⟩⟩
  refine ⟨fun N hnormal => ?_⟩
  let := hnormal
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  have hM := co3_normal_contains_mathieu N hN
  rcases triangle_stabilizer_maximal.le_iff.mp hM with ht | he
  · exact ht
  · let := faithful
    let := primitive
    have hn := Atlas.GroupTheory.normal_pretransitive (X := Points) N hN
    rw [he] at hn
    exact False.elim (co3_triangle_stabilizer_not_transitive hn)

end Atlas.Conway
