module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.SylowCoordinates
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.CharacteristicControl.Setup
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.CharacteristicControl.RadicalRestriction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.CharacteristicControl.ThompsonImage

/-!
# Lifting Thompson quotient control to the first block Borel

Let R = O₂(XU), Q = O₂(K₁R), and S = U ∩ K₁. If Q ≤ R and
J(R)Q = SQ, every element of N_{K₁}(S) normalizes J(R)Q and hence sends
J(R) into R. Weak closure of the elementary Thompson subgroup makes it
normalize J(R). This nontrivial characteristic subgroup of R therefore
places the entire Sylow normalizer, and in particular its two-residual,
in C(G,R).

For the commuting exchanged blocks, radical restriction proves Q ≤ R,
and the natural-module Thompson-image calculation proves J(R)Q = SQ.
Combining these results discharges both hypotheses of the lifting step
and establishes the first Sylow-normalizer residual containment from
the contrary data alone. The full pair Borel is assembled by the parent.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the
normalizer calculation (*) in the proof of C.2.7, printed p.146,
and the characteristic-two paragraph of the proof of 15.4.20, p.1164.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel
open Subgroup Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}
variable (c : ContraryData κ d i j)

/-- The quotient calculation lifts to literal normalization of the
nontrivial characteristic subgroup J(R). -/
theorem firstSylowNormalizer_normalizes_coreThompson_of_quotient
    (b : ExchangedBlock c)
    (hQ : blockRadicalCore b ≤ contraryCore c)
    (hJ : coreThompson c ⊔ blockRadicalCore b =
      (c.U ⊓ b.first) ⊔ blockRadicalCore b) :
    (firstSylowNormalizer b).map b.first.subtype ≤
      normalizer (coreThompson c : Set G) := by
  have hS : (firstSylowNormalizer b).map b.first.subtype ≤
      normalizer ((c.U ⊓ b.first : Subgroup G) : Set G) := by
    simpa only [firstSylowNormalizer, subgroupOf_map_subtype] using
      (c.U.subgroupOf b.first).le_normalizer_map b.first.subtype
  have hNQ : b.first ≤ normalizer (blockRadicalCore b : Set G) :=
    first_normalizes_blockRadicalCore c b
  have hN : (firstSylowNormalizer b).map b.first.subtype ≤
      normalizer ((coreThompson c ⊔ blockRadicalCore b : Subgroup G) : Set G) := by
    rw [hJ]
    exact (le_inf hS ((map_subtype_le _).trans hNQ)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply elementaryAbelianMaxJ_map_eq_of_le (contraryCore c) (MulAut.conj x)
  exact ((map_mono (show coreThompson c ≤ coreThompson c ⊔ blockRadicalCore b from
    le_sup_left)).trans (mem_normalizer_iff_map_conj_eq.mp (hN hx)).le).trans
      (sup_le (coreThompson_le c) hQ)

/-- Conditional residual containment, with both local pushing-up
obligations displayed explicitly. -/
theorem firstSylowResidual_le_of_thompson_quotient
    (b : ExchangedBlock c)
    (hQ : blockRadicalCore b ≤ contraryCore c)
    (hJ : coreThompson c ⊔ blockRadicalCore b =
      (c.U ⊓ b.first) ⊔ blockRadicalCore b) :
    firstSylowResidual b ≤ characteristicNormalizerClosure (contraryCore c) := by
  apply le_trans (map_mono (map_subtype_le (pResidual 2 (firstSylowNormalizer b))))
  exact (firstSylowNormalizer_normalizes_coreThompson_of_quotient c b hQ hJ).trans
    (coreThompson_normalizer_le c)

/-- The first block's intrinsic Sylow-normalizer two-residual lies in C(G,R),
with R = O₂(XU). Radical restriction and the actual natural-module action
discharge the local-core and Thompson-image premises of the lifting argument. -/
theorem firstSylowResidual_le_characteristicNormalizerClosure
    (b : ExchangedBlock c)
    (hc : ⁅b.first, BorelPlacement.ExchangedBlock.second b⁆ = ⊥) :
    firstSylowResidual b ≤
      characteristicNormalizerClosure ((d.wholeX ⊔ c.U : Subgroup G).pCoreIn 2) := by
  have hQ := blockRadicalCore_le_contraryCore c b hc
  exact firstSylowResidual_le_of_thompson_quotient c b hQ
    (coreThompson_sup_blockRadicalCore b hc hQ)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel
