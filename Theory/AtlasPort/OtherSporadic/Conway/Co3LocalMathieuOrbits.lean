/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3LocalMathieuOrbits.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3FusionFixedPoint
public import Theory.AtlasPort.OtherSporadic.Mathieu.OctadMixedFlagTransport
public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu21PointStabilizer
public import Theory.AtlasPort.OtherSporadic.Mathieu.OctadPairCounts
/-!
The norm-six stabilizer acting on decompositions into minimum Leech vectors.
The proofs connect the concrete coordinate action with Mathieu incidence geometry.

Source: Gerald Höhn, `Atlas/Conway/Co3LocalMathieuOrbits.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
set_option synthInstance.maxHeartbeats 200000
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable
local instance co3LocalOrbitPointsFintype (a : Omega) : Fintype (Mathieu23Points a) := Fintype.ofFinite _

abbrev Co3Heptads (a : Omega) := {B // B ∈ mathieu23Blocks a}

def co3LocalType (a : Omega) (b : Mathieu23Points a) : Co3PointHeptad a → Fin 4
  | Sum.inl c => if c = b then 0 else 1
  | Sum.inr B => if b ∈ B.val then 2 else 3

theorem co3_heptad_pair_transporter (a : Omega) (b : Mathieu23Points a)
    (B C : Co3Heptads a) (hbc : b ∈ B.val ↔ b ∈ C.val) :
    ∃ p : Mathieu23PointModel a, p • b = b ∧
      co3PointHeptadMap a p (Sum.inr B) = Sum.inr C := by
  let O := insert a (mathieu23BlockLift a B.val)
  let P := insert a (mathieu23BlockLift a C.val)
  have hO : O ∈ octads := (mathieu23Blocks_mem a B.val).mp B.prop
  have hP : P ∈ octads := (mathieu23Blocks_mem a C.val).mp C.prop
  have hmem (D : Co3Heptads a) : b.val ∈ insert a (mathieu23BlockLift a D.val) ↔ b ∈ D.val := by
    simp [mathieu23BlockLift,(show b.val ≠ a from b.prop)]
  have he : ∃ g : Mathieu24CodeModel, permuteBlock g.val O = P ∧ g.val a = a ∧ g.val b.val = b.val := by
    by_cases hb : b ∈ B.val
    · obtain ⟨g,hg,hgO⟩ := mathieu24_marked_octad_transitive {a,b.val} O P
        (by rw [Finset.card_pair (show a ≠ b.val from (show b.val ≠ a from b.prop).symm)]; decide) hO hP
        (Finset.insert_subset (Finset.mem_insert_self _ _) (Finset.singleton_subset_iff.mpr ((hmem B).mpr hb)))
        (Finset.insert_subset (Finset.mem_insert_self _ _) (Finset.singleton_subset_iff.mpr ((hmem C).mpr (hbc.mp hb))))
      exact ⟨g,hgO,hg a (by simp),hg b.val (by simp)⟩
    · exact mathieu24_octad_mixed_flag_transitive O P hO hP a b.val a b.val
        (Finset.mem_insert_self _ _) (fun h => hb ((hmem B).mp h))
        (Finset.mem_insert_self _ _) (fun h => hb (hbc.mpr ((hmem C).mp h)))
  obtain ⟨g,hg,ha,hb⟩ := he
  let p : Mathieu23PointModel a := ⟨g,ha⟩
  refine ⟨p,Subtype.ext hb,congrArg Sum.inr (Subtype.ext ?_)⟩
  ext i
  have h := Iff.of_eq (congrArg (fun T : Finset Omega => i.val ∈ T) hg)
  have hh : insert a (mathieu23BlockLift a (mathieu23PermuteBlock a p B.val)) = permuteBlock g.val O := by
    rw [mathieu23BlockLift_permute]
    simp [permuteBlock,p,O,ha]
  rw [← hh] at h
  simpa [P,mathieu23BlockLift,(show i.val ≠ a from i.prop)] using h

theorem co3_local_mathieu_transitive (a : Omega) (b : Mathieu23Points a)
    (q r : Co3PointHeptad a) (he : co3LocalType a b q = co3LocalType a b r) :
    ∃ p : Mathieu23PointModel a, p • b = b ∧ co3PointHeptadMap a p q = r := by
  cases q with
  | inl c =>
    cases r with
    | inl d =>
      by_cases hc : c = b
      · have hd : d = b := by simpa [co3LocalType,hc] using he
        subst c; subst d
        exact ⟨1,one_smul _ _,congrArg Sum.inl (one_smul _ _)⟩
      · have hd : d ≠ b := by simpa [co3LocalType,hc] using he
        let := mathieu22_pretransitive a b
        obtain ⟨p,hp⟩ := MulAction.exists_smul_eq (Mathieu22PointModel a b)
          (⟨c,hc⟩ : Mathieu22Points a b) (⟨d,hd⟩ : Mathieu22Points a b)
        exact ⟨p.val,p.prop,congrArg Sum.inl (congrArg Subtype.val hp)⟩
    | inr D => simp only [co3LocalType] at he; split_ifs at he <;> contradiction
  | inr C =>
    cases r with
    | inl d => simp only [co3LocalType] at he; split_ifs at he <;> contradiction
    | inr D =>
      apply co3_heptad_pair_transporter a b C D
      simp only [co3LocalType] at he
      by_cases hC : b ∈ C.val <;> by_cases hD : b ∈ D.val <;> simp_all

end Atlas.Conway
