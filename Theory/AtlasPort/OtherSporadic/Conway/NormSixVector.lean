/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/NormSixVector.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.LeechOrthogonalComplement
public import Theory.AtlasPort.OtherSporadic.Conway.AntipodalStabilizer
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechOddProfiles
public import Theory.AtlasPort.OtherSporadic.Sporadic.Mathieu23
/-!
The concrete norm-six Leech shell and its stabilizers.
Coordinate orbit transport and orbit-stabilizer counting identify the full stabilizer.

Source: Gerald Höhn, `Atlas/Conway/NormSixVector.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

/-- A norm-six vector with numerator coordinates (5,1,...,1). -/
def normSixVector (a : Omega) : leech :=
  ⟨signedOddProfile ∅ {a} 0,signedOddProfile_mem _ _ (by simp) 0⟩

theorem normSixVector_apply (a i : Omega) :
    (normSixVector a).val i = if i = a then 5 else 1 := by
  by_cases h : i = a <;> simp [normSixVector,signedOddProfile,signChange,oddProfileBase,h]

theorem normSixVector_norm (a : Omega) :
    integerDot (normSixVector a).val (normSixVector a).val = 48 := by
  simpa [normSixVector] using signedOddProfile_norm ∅ {a} (by simp) (0 : golay)

theorem normSixVector_ne_zero (a : Omega) : normSixVector a ≠ 0 := by
  intro h
  have hh := normSixVector_norm a
  rw [h] at hh
  norm_num [integerDot] at hh

theorem permutation_normSixVector (g : Mathieu24CodeModel) (a : Omega) :
    (permutationEmbedding g).val (normSixVector a) = normSixVector (g.val a) := by
  apply Subtype.ext
  funext i
  change (normSixVector a).val (g.val.symm i) = _
  simp only [normSixVector_apply,Equiv.symm_apply_eq]

def mathieu23ToNormSixStabilizer (a : Omega) :
    Mathieu23PointModel a →* fullVectorStabilizer (normSixVector a) where
  toFun g := ⟨permutationEmbedding g.val,by
    change (permutationEmbedding g.val).val (normSixVector a) = normSixVector a
    rw [permutation_normSixVector]
    exact congrArg normSixVector g.prop⟩
  map_one' := Subtype.ext (permutationEmbedding.map_one)
  map_mul' g h := Subtype.ext (permutationEmbedding.map_mul g.val h.val)

theorem mathieu23ToNormSixStabilizer_injective (a : Omega) :
    Function.Injective (mathieu23ToNormSixStabilizer a) := by
  intro g h he
  apply Subtype.ext
  apply permutationEmbedding_injective
  exact congrArg (fun x : fullVectorStabilizer (normSixVector a) => x.val) he

end Atlas.Conway
