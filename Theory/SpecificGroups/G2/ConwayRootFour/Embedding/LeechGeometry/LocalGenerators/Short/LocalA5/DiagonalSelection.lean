module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.Data
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.OrderObstruction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.DiagonalSelection.Transport
/-!
# Ambient selection of the short-root diagonal

The common flip and inverted cubic torus restrict the image of the upper
shear to the upper or lower shear. In the lower case, a word in the supplied
local lift, graph element, and four long blocks has a coordinate action whose
square has order seventeen. That is impossible in the literal Leech central
quotient by its proved order. Hence the twist fixes the upper shear.

This proves the conditional identification from Data L and applies it to the
parent's marked short-root seed. Construction of Data L remains with the local
A₅ geometry owner. No faithfulness of the entire centralizer is required.

Source: Aschbacher, Sporadic Groups (1994), Lemma 49.5, p.284. The ambient
argument repairs the source's asserted uniqueness from the common S₃;
DiagonalAmbiguity shows why that restriction alone is insufficient.
-/

public section

open Atlas.Conway
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5
open OctonionLocals
open PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight
namespace DiagonalSelection

private theorem realizes_mul {L : LongFrame} {g h : LeechCentralQuotient}
    {a b : LinearGroup}
    (ha : ∀ v, quotientModTwoRepresentation g (L.coordinates v) = L.coordinates (a v))
    (hb : ∀ v, quotientModTwoRepresentation h (L.coordinates v) = L.coordinates (b v)) :
    ∀ v, quotientModTwoRepresentation (g*h) (L.coordinates v) = L.coordinates ((a*b) v) := by
  intro v
  simp only [map_mul, LinearEquiv.mul_apply]
  rw [hb, ha]

/-- The lower-shear alternative forces a forbidden element of order seventeen
through exactly the supplied block and graph lifts. -/
theorem not_lower {L : LongFrame} (D : Data L) : D.twist shear ≠ lowerShear := by
  intro hbad
  let e := fieldEquiv.toRingHom
  let block (A : SL(3,K)) := L.long (Matrix.SpecialLinearGroup.map e A)
  let step (A : SL(3,K)) := D.lift shear * L.swap * block A
  let g := step Certificate.A0 * step Certificate.A1 * step Certificate.A2 * step Certificate.A3
  have hb : ∀ v, quotientModTwoRepresentation (D.lift shear) (L.coordinates v) =
      L.coordinates (pairRepresentation (shear, lowerShear) v) := by
    intro v
    rw [D.on_action, hbad]
  have hg : ∀ v, quotientModTwoRepresentation L.swap (L.coordinates v) =
      L.coordinates (action graph v) := equivariant_of_single _ _ _ L.on_swap
  have hl (A : SL(3,K)) : ∀ v,
      quotientModTwoRepresentation (block A) (L.coordinates v) =
      L.coordinates (action (BlockRealization.blockHom (Matrix.SpecialLinearGroup.map e A)) v) :=
    L.intertwines_long _
  have hs (A : SL(3,K)) := realizes_mul (realizes_mul hb hg) (hl A)
  have hw : ∀ v, quotientModTwoRepresentation g (L.coordinates v) =
      L.coordinates (coordinateWord e v) :=
    realizes_mul (realizes_mul (realizes_mul (hs Certificate.A0) (hs Certificate.A1))
      (hs Certificate.A2)) (hs Certificate.A3)
  have hsq : ∀ v, quotientModTwoRepresentation (g^2) (L.coordinates v) =
      L.coordinates ((coordinateWord e ^ 2) v) := by
    simpa only [pow_two] using realizes_mul hw hw
  exact no_order_seventeen L (g^2) (coordinateWord e ^ 2) hsq (coordinateWord_order e)

end DiagonalSelection

/-- The actual ambient quotient selects the upper shear. The common S₃ alone
only restricts its image to the upper or lower shear. -/
theorem Data.twist_shear {L : LongFrame} (D : Data L) : D.twist shear = shear := by
  rcases DiagonalSelection.data_shear_alternatives D with h | h
  · exact h
  · exact False.elim (DiagonalSelection.not_lower D h)

/-- Application to the parent's literal marked short-root seed. Construction
of `Data L` remains the separate local-geometry obligation. -/
theorem Data.scalar_short_seed {L : LongFrame} (D : Data L) :
    ∃ g ∈ centralizerI, L.Intertwines g (Atlas.G2.rootC 1) ∧
      IsConj g scalarInvolution :=
  D.scalar_short_seed_of_twist_shear D.twist_shear

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5
