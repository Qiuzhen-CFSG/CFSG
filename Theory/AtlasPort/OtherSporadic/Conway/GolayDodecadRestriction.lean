/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/GolayDodecadRestriction.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.GolayOctadExteriorRestriction
public import Theory.AtlasPort.OtherSporadic.Codes.GolayDistribution
/-!
Golay coordinate restrictions and signed-support transport in the Leech lattice.
The proofs retain the explicit code maps and coordinate identities used by the stabilizer geometry.

Source: Gerald Höhn, `Atlas/Conway/GolayDodecadRestriction.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem golay_supported_dodecad (D : Finset Omega) (hD : D.card = 12)
    (hC : supportWord D ∈ golay) (w : BinaryWord) (hw : w ∈ golay)
    (hs : support w ⊆ D) : w = 0 ∨ w = supportWord D := by
  by_cases hz : w = 0
  · exact Or.inl hz
  right
  have hle : hammingNorm w ≤ 12 := (Finset.card_le_card hs).trans_eq hD
  have hmin := golay_minimum w hw hz
  have hweights := golay_weights ⟨w,hw⟩
  have hsupport : support (supportWord D) = D := binarySupportEquiv.right_inv D
  have hweight : hammingNorm (supportWord D) = 12 :=
    (congrArg Finset.card hsupport).trans hD
  have hadd := binary_weight_add (supportWord D) w
  rw [overlap_inter,hsupport,Finset.inter_eq_right.mpr hs,hweight] at hadd
  have hsum := golay_weights ⟨supportWord D + w,golay.add_mem hC hw⟩
  have he : hammingNorm w = 12 := by
    change hammingNorm (supportWord D + w) + 2 * hammingNorm w = 12 + hammingNorm w at hadd
    change hammingNorm w = 0 ∨ hammingNorm w = 8 ∨ hammingNorm w = 12 ∨
      hammingNorm w = 16 ∨ hammingNorm w = 24 at hweights
    change hammingNorm (supportWord D + w) = 0 ∨ hammingNorm (supportWord D + w) = 8 ∨
      hammingNorm (supportWord D + w) = 12 ∨ hammingNorm (supportWord D + w) = 16 ∨
      hammingNorm (supportWord D + w) = 24 at hsum
    omega
  have hB : support w = D := Finset.eq_of_subset_of_card_le hs (by change D.card ≤ hammingNorm w; omega)
  have hh := binarySupportEquiv.left_inv w
  change supportWord (support w) = w at hh
  rw [hB] at hh
  exact hh.symm

theorem golay_dodecad_erased_surjective (D : Finset Omega) (hD : D.card = 12)
    (hC : supportWord D ∈ golay) (a : Omega) (ha : a ∈ D) :
    Function.Surjective (golayRestriction (D.erase a)) := by
  apply golay_restriction_surjective_of_no_support
  intro w hw hs
  rcases golay_supported_dodecad D hD hC w hw (hs.trans (Finset.erase_subset _ _)) with h | h
  · exact h
  · have hsupport : support w = D := h ▸ binarySupportEquiv.right_inv D
    have hh : a ∈ support w := hsupport ▸ ha
    exact False.elim ((Finset.mem_erase.mp (hs hh)).1 rfl)

theorem golay_dodecad_restriction (D : Finset Omega) (hD : D.card = 12)
    (hC : supportWord D ∈ golay) (w : BinaryWord) (hw : ∑ i ∈ D, w i = 0) :
    ∃ c : golay, ∀ i ∈ D, c.val i = w i := by
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < D.card)
  obtain ⟨c,hc⟩ := golay_dodecad_erased_surjective D hD hC a ha (fun i => w i)
  have he (i : Omega) (hi : i ∈ D.erase a) : c.val i = w i := congrFun hc ⟨i,hi⟩
  have hp := golay_selfOrthogonal hC c.val c.prop
  change binaryDot c.val (supportWord D) = 0 at hp
  rw [tetradSignParity_dot,tetradSignParity,Finset.sum_coe_sort] at hp
  have hcSum : (∑ i ∈ D.erase a, c.val i) = ∑ i ∈ D.erase a, w i := Finset.sum_congr rfl he
  have hae : c.val a = w a := by
    rw [← Finset.add_sum_erase _ _ ha,hcSum] at hp
    rw [← Finset.add_sum_erase _ _ ha] at hw
    exact add_right_cancel (hp.trans hw.symm)
  refine ⟨c,?_⟩
  intro i hi
  by_cases hia : i = a
  · simpa [hia] using hae
  exact he i (Finset.mem_erase.mpr ⟨hia,hi⟩)

end Atlas.Conway
