module

public import Theory.Representation.MathieuCodeRestriction.Construction
public import Theory.AtlasPort.OtherSporadic.Mathieu.GolayAutomorphisms

/-!
# Comparing the native and ATLAS binary Golay codes

An explicit coordinate bijection sends each of the twelve ATLAS Golay basis
words to a certified native codeword. The two spaces have dimension twelve,
so this containment is equality. Restriction gives a linear equivalence of
the actual codes, compatible with conjugating coordinate permutations.

The ATLAS construction and octad basis are reused from
`Theory.AtlasPort.OtherSporadic.Codes.GolayBasis`, originally
`Atlas/Codes/GolayBasis.lean`, Gerald Höhn and ATLAS contributors, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`, under the ATLAS Research and
Attribution License 1.0 (see `LICENSES/ATLAS.txt`). The explicit comparison
with the native Witt-design coordinates is proved here.

Source for the required Golay module: Aschbacher–Smith, H.13.1,
printed p.395. No abstract isomorphism of unconnected model tags is used.
-/

@[expose] public section

open Sporadic.Mathieu
open scoped BigOperators
namespace MathieuCode
noncomputable section

/-- Reorder the flattened ATLAS tetrad coordinates into native coordinates. -/
def atlasCoordinatePermutation : Equiv.Perm (Fin 24) where
  toFun := ![0,1,2,3,4,5,17,11,6,14,9,19,12,15,20,7,23,16,10,22,18,13,21,8]
  invFun := ![0,1,2,3,4,5,8,15,23,10,18,7,12,21,9,13,17,6,20,11,14,22,19,16]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- The ATLAS six-tetrad coordinate set identified with the native 24 points. -/
def atlasPointEquiv : Atlas.Codes.Omega ≃ Fin 24 :=
  ((Equiv.prodCongr Atlas.Codes.hexIndexEquiv (Equiv.refl (Fin 4))).trans
    finProdFinEquiv).trans atlasCoordinatePermutation

/-- The induced coordinate change on the full binary permutation spaces. -/
def atlasWordEquiv : Atlas.Codes.BinaryWord ≃ₗ[ZMod 2] Full :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) atlasPointEquiv.symm

theorem atlasWordEquiv_apply (w : Atlas.Codes.BinaryWord) (i : Fin 24) :
    atlasWordEquiv w i = w (atlasPointEquiv.symm i) := rfl

def atlasRowMessage : Fin 12 → Fin 4096 :=
  ![1578,140,2828,1676,1292,266,1087,591,143,15,2319,2385]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem atlasGenerator_eq_native (i : Fin 12) :
    atlasWordEquiv (Atlas.Codes.golayGenerators i) =
      wordOfMask (m24GolayCode (atlasRowMessage i)) := by
  fin_cases i <;> decide +kernel

theorem atlasWordEquiv_mem_golay {w : Atlas.Codes.BinaryWord}
    (hw : w ∈ Atlas.Codes.golay) : atlasWordEquiv w ∈ golay := by
  have he := congrArg (fun v : Atlas.Codes.golay => atlasWordEquiv v.val)
    (Atlas.Codes.golayBasis.sum_repr ⟨w,hw⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
    Atlas.Codes.golayBasis_coe] at he
  rw [← he]
  exact golay.sum_mem fun i _ => golay.smul_mem _
    (by rw [atlasGenerator_eq_native]; exact wordOfMask_code_mem _)

/-- The coordinate change identifies the actual Golay subspaces. -/
theorem atlas_golay_map :
    Atlas.Codes.golay.map atlasWordEquiv.toLinearMap = golay := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨w, hw, rfl⟩
    exact atlasWordEquiv_mem_golay hw
  · rw [atlasWordEquiv.finrank_map_eq, Atlas.Codes.golay_finrank, finrank_golay]

/-- The genuine linear equivalence between the two concrete Golay codes. -/
def atlasGolayEquiv : Atlas.Codes.golay ≃ₗ[ZMod 2] golay :=
  atlasWordEquiv.ofSubmodules _ _ atlas_golay_map

theorem atlasGolayEquiv_apply (w : Atlas.Codes.golay) :
    (atlasGolayEquiv w).val = atlasWordEquiv w.val := rfl

theorem atlasWordEquiv_permute (g : Equiv.Perm (Fin 24))
    (w : Atlas.Codes.BinaryWord) :
    atlasWordEquiv (Atlas.Codes.coordinatePermutation
      (atlasPointEquiv.symm.permCongr g) w) =
      BinaryPermutation.representation (Fin 24) g (atlasWordEquiv w) := by
  have hperm (σ : Equiv.Perm Atlas.Codes.Omega) (u : Atlas.Codes.BinaryWord)
      (p : Atlas.Codes.Omega) : Atlas.Codes.coordinatePermutation σ u p = u (σ.symm p) := rfl
  ext i
  simp only [atlasWordEquiv_apply, hperm, BinaryPermutation.representation_apply,
    Equiv.permCongr_def, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply]

theorem mem_atlas_golay_iff (w : Atlas.Codes.BinaryWord) :
    w ∈ Atlas.Codes.golay ↔ atlasWordEquiv w ∈ golay := by
  constructor
  · exact atlasWordEquiv_mem_golay
  · intro hw
    rw [← atlas_golay_map] at hw
    obtain ⟨v, hv, he⟩ := hw
    exact atlasWordEquiv.injective he ▸ hv

end
end MathieuCode
