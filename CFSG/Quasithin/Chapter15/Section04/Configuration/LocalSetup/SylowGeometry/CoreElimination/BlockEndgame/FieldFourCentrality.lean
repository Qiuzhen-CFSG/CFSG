module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.FieldFourCentrality.Reduction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.FieldFourCentrality.RadicalLayer
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.FieldFourCentrality.SourceCubicActor

/-!
# The fixed-seed centrality assembly

The source conjugate closure is elementary with displacement in U(L).
Commutation of the actual exchanged blocks makes the source X-factors
normalize L and supplies a genuine cubic actor. On the natural block module,
this actor fixes only zero; the odd-orbit argument then proves that the
fixed seed C_Z(X) centralizes L.

This completes the centrality deduction for the supplied contrary geometry
and exchanged block with n = 2. All four structural inputs in the reduction
are discharged. The field bound remains a separate deduction in the parent
endgame; no 15.4.21–23 input is used.

Source: Aschbacher–Smith, proof of 15.4.20, printed p.1164.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.FieldFourCentrality
open Subgroup
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}

/-- Assembly from the elementary radical layer and the actual cubic source action. -/
theorem fixed_seed_centralizes_first_of_structural_inputs
    (c : ContraryData κ d i j) (b : ExchangedBlock c)
    (helem : IsElementaryAbelian 2 (seedClosure c))
    (hdisp : ⁅seedClosure c, b.first⁆ ≤ firstLayer b)
    (hnorm : d.wholeX ≤ normalizer (b.first : Set G))
    (hcubic : HasCubicActor c b) :
    d.Z ⊓ centralizer (d.wholeX : Set G) ≤ centralizer (b.first : Set G) := by
  obtain ⟨F, _, _, _, _, _, ⟨m⟩⟩ := even_block_model b.model
  exact fixed_seed_centralizes_first_of_layer c b helem hdisp hnorm
    (layer_fixed_of_cubic_actor c b m hcubic)

/-- The fixed seed centralizes the actual exchanged `L₂(4)` block.
The elementary radical layer and cubic source action follow from the supplied
source geometry and relative block structure. -/
theorem fixed_seed_centralizes_first
    (c : ContraryData κ d i j) (b : ExchangedBlock c) (hn : b.n = 2) :
    d.Z ⊓ centralizer (d.wholeX : Set G) ≤ centralizer (b.first : Set G) := by
  obtain ⟨hnorm, hcubic⟩ := fieldFour_normalization_and_cubic_actor c b hn
  exact fixed_seed_centralizes_first_of_structural_inputs c b
    (seedClosure_elementary c) (seedClosure_commutator_le_firstLayer c b) hnorm hcubic

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.FieldFourCentrality
