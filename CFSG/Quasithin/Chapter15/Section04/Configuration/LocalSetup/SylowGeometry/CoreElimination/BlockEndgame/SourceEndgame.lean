module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.FieldFourCentrality

/-!
# The surviving exchanged-block contradiction in 15.4.20

The genuine exchanged blocks commute. Their intrinsic Sylow normalizers
therefore construct a compatible pair Borel inside the characteristic
normalizer closure of R = O₂(XU). The source uniqueness condition puts that
Borel in M₁. Its action on the actual four-group forces the field parameter
to be two. The proved field-four argument then makes C_Z(X) centralize the
first block, hence its conjugate and H = KU, contradicting the outside
Y-factor.

All commutation, Borel-placement, field-bound and fixed-seed centrality
premises are discharged. The input retains the original contrary Sylow
geometry and the actual block produced by the independent module sieve.
No conclusion from 15.4.21–23 or `Source.LocalData` is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the final
characteristic-two paragraph of 15.4.20, printed p.1164.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame

open Subgroup

variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}

/-- The actual exchanged block has field order four, with the Borel
construction and exchanged-block commutation supplied by their source proofs. -/
theorem source_parameter_eq_two (c : ContraryData κ d i j) (b : ExchangedBlock c) :
    b.n = 2 := by
  have hc : ⁅b.first, BorelPlacement.ExchangedBlock.second b⁆ = ⊥ :=
    FieldFourCentrality.exchanged_blocks_commute c b
  obtain ⟨F, hF, hfin, hchar, hcard, m, hB⟩ :=
    BorelPlacement.ControlledBorel.exists_controlled_model b hc
  exact BorelPlacement.parameter_eq_two_of_characteristic_control c b hc m hcard hB

/-- The original fixed seed is central in H, on its literal ambient image. -/
theorem source_fixed_seed_le_center (c : ContraryData κ d i j) (b : ExchangedBlock c) :
    d.Z ⊓ centralizer (d.wholeX : Set G) ≤ (center c.H).map c.H.subtype :=
  c.fixed_seed_le_center_H b
    (FieldFourCentrality.fixed_seed_centralizes_first c b (source_parameter_eq_two c b))

/-- The surviving exchanged-block branch of the contrary Sylow argument is
impossible. No Borel, field-four or seed-centrality conclusion is assumed. -/
theorem source_contradiction (c : ContraryData κ d i j) (b : ExchangedBlock c) : False :=
  c.false_of_fixed_seed_centralizes_first b
    (FieldFourCentrality.fixed_seed_centralizes_first c b (source_parameter_eq_two c b))

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame
