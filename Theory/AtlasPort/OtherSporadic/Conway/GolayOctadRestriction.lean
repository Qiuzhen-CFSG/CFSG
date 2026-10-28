/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/GolayOctadRestriction.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.GolaySmallRestriction
/-!
Golay coordinate restrictions and signed-support transport in the Leech lattice.
The proofs retain the explicit code maps and coordinate identities used by the stabilizer geometry.

Source: Gerald Höhn, `Atlas/Conway/GolayOctadRestriction.lean`, ATLAS revision
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

theorem golay_octad_restriction (T : Finset Omega) (hT : T.card = 8)
    (hC : supportWord T ∈ golay) (w : BinaryWord) (hw : ∑ i ∈ T, w i = 0) :
    ∃ c : golay, ∀ i ∈ T, c.val i = w i := by
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  have hs : (T.erase a).card < 8 := by rw [Finset.card_erase_of_mem ha,hT]; decide
  obtain ⟨c,hc⟩ := golay_small_restriction_surjective (T.erase a) hs (fun i => w i)
  have he (i : Omega) (hi : i ∈ T.erase a) : c.val i = w i :=
    congrFun hc ⟨i,hi⟩
  have hp := golay_selfOrthogonal hC c.val c.prop
  change binaryDot c.val (supportWord T) = 0 at hp
  rw [tetradSignParity_dot,tetradSignParity,Finset.sum_coe_sort] at hp
  have hcSum : (∑ i ∈ T.erase a, c.val i) = ∑ i ∈ T.erase a, w i :=
    Finset.sum_congr rfl he
  have haeq : c.val a = w a := by
    rw [← Finset.add_sum_erase _ _ ha,hcSum] at hp
    rw [← Finset.add_sum_erase _ _ ha] at hw
    exact add_right_cancel (hp.trans hw.symm)
  refine ⟨c,?_⟩
  intro i hi
  by_cases hia : i = a
  · simpa [hia] using haeq
  · exact he i (Finset.mem_erase.mpr ⟨hia,hi⟩)

end Atlas.Conway
