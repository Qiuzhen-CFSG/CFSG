module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Models
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Diagonal
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Complement
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Center

/-!
# The intrinsic even rank-one block calculation

The actual quotient Borel is matched with the natural block module, and
Schur–Zassenhaus constructs a compatible diagonal section. Its range is the
cyclic complement X of the specified Sylow subgroup S in B. Coprime action
and odd-orbit averaging split Ω₁(Z(S)) into its global central part and
its displacement under X. Applying I.2.3 to the constructed natural cover
makes this displacement a full natural line, of order 2ⁿ; literal conjugation
by X is regular on its nonidentity elements. The quotient Borel gives
the index 2ⁿ + 1.

`exists_rankOneBlockTorus_of_I23` assembles all these conclusions from the
block and Borel hypotheses. Its only additional input is the explicit
rank-one specialization of I.2.3(1),(3), including the orthogonal universal
cover. That earlier source theorem remains for the source-theorem owner to
discharge. No torus or center conclusion is assumed, and C.1.13 is not used.

Source: Aschbacher–Smith, E.6.7, printed p.246, using C.1.12 and I.2.3,
printed pp.124 and 413.
-/

namespace CFSG.Quasithin.ChapterE.Section06

open Subgroup Theory.GroupTheory

universe u

/-- The full preimage of the genuine rank-one Borel has index `2^n + 1`. -/
public theorem L2BlockBorel.index {L : Type*} [Group L] {B : Subgroup L} {n : ℕ}
    (hB : L2BlockBorel L B n) : B.index = 2 ^ n + 1 := by
  obtain ⟨F, _, _, hF, e, rfl⟩ := hB
  rw [index_comap_of_surjective _
    (e.surjective.comp (QuotientGroup.mk'_surjective _)), L2Torus.index_borel, hF]

/-- The intrinsic L₂-block torus calculation used in E.6.7 and E.6.11.
The earlier-source hypothesis is I.2.3 for the natural binary covers over
fields of order `2^n`; the diagonal section and every torus conclusion are
constructed here from the block and its actual quotient Borel. -/
public theorem exists_rankOneBlockTorus_of_I23 {L : Type u} [Group L] [Finite L]
    {n : ℕ} (hL : ChapterC.IsL2EvenBlock L n)
    (S : Sylow 2 L) {B : Subgroup L} (hS : (S : Subgroup L) ≤ B)
    (hB : L2BlockBorel L B n)
    (hI23 : ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      L2Torus.CoverLift.RankOneCoverTheorem.{0, u} F n) :
    Nonempty (RankOneBlockTorus L S B n) := by
  obtain ⟨F, _, _, _, hF, ⟨a⟩⟩ := L2Torus.exists_markedBlockModel hL hB
  obtain ⟨d⟩ := L2Torus.exists_diagonalSection a
  obtain ⟨hdecomp, hdisjoint, hcard, hregular⟩ :=
    d.center_calculation_of_I23 hL.2.1 S hS hL.1 hF (hI23 F)
  exact ⟨{
    torus := d.torus
    le_borel := d.torus_le_borel
    cyclic := d.torus_cyclic
    order := by rw [d.torus_card, hF]
    normalizes_sylow := d.normalizes_sylow S hS
    borel_product := d.borel_product S hS
    disjoint_sylow := d.disjoint_sylow S hS
    center_decomposition := hdecomp
    center_disjoint := hdisjoint
    displacement_order := hcard
    regular := hregular
    borel_index := hB.index }⟩

end CFSG.Quasithin.ChapterE.Section06
