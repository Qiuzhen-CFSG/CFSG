module

public import Theory.Representation.HermitianTensorThree.UnipotentRadicals
public import Theory.Representation.BinaryOffender.RestrictionComparison

import all Theory.Representation.HermitianTensorThree.UnipotentRadicals

/-!
# Sylow fixed spaces in the Hermitian source module

Conjugate the actual image Sylow subgroup to the standard unipotent image.
Its point radical has an n-dimensional fixed space, bounding the Sylow fixed
space. In half-degree one this gives the fixed line used in 8.2.10(4).

The internal import reuses the existing Sylow construction and its exact map
identity; neither private construction appears in the exported statement.
Source: Aschbacher–Smith H.4.4 and 8.2.10(4), printed pp.381 and 721,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
local instance (n : ℕ) [NeZero n] : Finite (Space n ≃ₗ[ZMod 2] Space n) :=
  Finite.of_injective (fun e : Space n ≃ₗ[ZMod 2] Space n => (e : Space n → Space n))
    DFunLike.coe_injective

/-- The point radical already bounds the fixed space of any Sylow subgroup. -/
theorem finrank_sylow_fixed_le (n : ℕ) [NeZero n] (S : Sylow 2 (binaryImage n)) :
    Module.finrank (ZMod 2) (fixedSpace (overgroupAction n (binaryImage n)) S) ≤ n := by
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq (binaryImage n)
    (UnipotentRadicals.imageSylow n) S
  change Module.finrank (ZMod 2) (fixedSpace (overgroupAction n (binaryImage n))
    ((UnipotentRadicals.imageSylow n : Subgroup (binaryImage n)).map
      (MulAut.conj g).toMonoidHom)) ≤ n
  rw [←(fixedSpaceConjEquiv (overgroupAction n (binaryImage n))
    (UnipotentRadicals.imageSylow n) g).finrank_eq]
  change Module.finrank (ZMod 2) (fixedSpace
    ((UnipotentRadicals.ambientAction n).comp (binaryImage n).subtype)
    (UnipotentRadicals.imageSylow n)) ≤ n
  rw [fixedSpace_comp_map,UnipotentRadicals.imageSylow_map]
  exact (Submodule.finrank_mono (fixedSpace_antitone (UnipotentRadicals.ambientAction n)
    (show UnipotentRadicals.point n ≤ (UnipotentRadicals.unipotentHom n).range from
      map_le_range _ _))).trans_eq (UnipotentRadicals.finrank_point_fixed n)
end CFSG.Quasithin.Chapter8.Section02.HermitianSource
