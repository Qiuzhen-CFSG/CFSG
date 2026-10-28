module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.Reduction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.DiagonalSelection.Relations

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.InverterCoset.AmbientDiagonal
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.InverterCoset.FactorActions

/-!
# The placed J₂ inverter lies in the long-cubic graph coset

The two subgroup marks place the literal J₂ dihedral centralizer, an A₅,
inside the matrix centralizer of D₁₀. Its two SL₂(4) projections are
isomorphisms because the placed cubic acts nontrivially on each factor.
The comparison of these projections inverts the torus.

The ambient order obstruction makes the subgroup of realized matrix pairs
proper. Maximality of a full diagonal then forces the comparison to fix the
frame's graph reflection. Finally the J₂ inverter inverts the marked cubic;
the elementary SL₂(4) torus-normalizer calculation places its first projection
in `torus t * flip`. The comparison gives exactly the inverse parameter in
the second projection, hence the asserted long-cubic graph action.

This proves the inverter premise consumed by `RootJ2Alignment` without any
faithfulness assumption, equality with `L.swap`, or additional frame provenance.
The general placement theorem below is applied to the literal conjugated
icosian embedding. Source: Aschbacher, *Sporadic Groups* (1994), 49.5,
pp.283–284, with placement from 48.8, p.273. The ambient argument avoids
the common-S₃ uniqueness inference discussed in `LocalA5.DiagonalAmbiguity`.
-/

open Matrix Atlas.Conway Atlas.Algebra
open scoped MatrixGroups
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.InverterCoset

local instance : CharP GoldenFour 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) GoldenFour).injective 2

private theorem golden_inverter_coset : ∀ a : SL(2,GoldenFour),
    a * DiagonalSelection.cubic * a⁻¹ = DiagonalSelection.cubic⁻¹ →
      ∃ t : GoldenFourˣ, a = torus t * flip := by decide +kernel

theorem torus_inverter_coset (a : SL(2,F))
    (ha : ∀ t : Fˣ, a * torus t * a⁻¹ = (torus t)⁻¹) :
    ∃ t : Fˣ, a = torus t * flip := by
  have h : slEquiv.symm a * DiagonalSelection.cubic * (slEquiv.symm a)⁻¹ =
      DiagonalSelection.cubic⁻¹ := by
    apply slEquiv.injective
    rw [map_mul, map_mul, map_inv, map_inv, slEquiv.apply_symm_apply]
    have hc : slEquiv DiagonalSelection.cubic =
        torus (Units.map fieldEquiv.toRingHom DiagonalSelection.cubicUnit) :=
      DiagonalSelection.slMap_torus fieldEquiv.toRingHom _
    rw [hc]
    exact ha _
  obtain ⟨t,ht⟩ := golden_inverter_coset (slEquiv.symm a) h
  refine ⟨Units.map fieldEquiv.toRingHom t, ?_⟩
  have he := congrArg slEquiv ht
  rw [slEquiv.apply_symm_apply, map_mul] at he
  exact he.trans (congrArg₂ (· * ·)
    (DiagonalSelection.slMap_torus fieldEquiv.toRingHom t)
    (DiagonalSelection.slMap_flip fieldEquiv.toRingHom))


open Sporadic.LeechRelated.J2.RecognitionGeometry (K X x)

private def sourceInverter : K :=
  ⟨Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5.inverter,
    Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5.inverter_mem_K⟩

private theorem sourceInverter_inverts (a : K)
    (ha : (a : Sporadic.LeechRelated.J2.Carrier) ∈ X) :
    sourceInverter * a * sourceInverter⁻¹ = a⁻¹ := by
  apply Subtype.ext
  obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp ha
  change Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5.inverter *
    (a : Sporadic.LeechRelated.J2.Carrier) *
    Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5.inverter⁻¹ =
      (a : Sporadic.LeechRelated.J2.Carrier)⁻¹
  rw [← hn]
  change MulAut.conj Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5.inverter
    (x ^ n) = (x ^ n)⁻¹
  rw [map_zpow, Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5.inverter_conj_x,
    inv_zpow]

variable {L : LongFrame}
    {f : Sporadic.LeechRelated.J2.Carrier →* LeechCentralQuotient}

theorem rootPair_realized (M : RootJ2SubgroupMarks L f)
    (hf : ∀ a, f a ∈ centralizerI) (a : SL(2,F)) :
    (a, twist M hf a) ∈ realizedPairs L := by
  refine ⟨f ((first M hf).symm a), fun v => ?_⟩
  rw [rootPair_action M hf, rootPair_eq, MulEquiv.apply_symm_apply]

/-- Subgroup marks alone suffice: the literal J₂ centralizer and the ambient
Leech order supply the missing compatibility of the two matrix factors. -/
theorem placed_inverter_action_coset (M : RootJ2SubgroupMarks L f)
    (hf : ∀ a, f a ∈ centralizerI) :
    ∃ t : Fˣ, ∀ v : Fin 6 → F,
      quotientModTwoRepresentation
        (f Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5.inverter) (L.coordinates v) =
      quotientModTwoRepresentation (longCubic L t)
        (L.coordinates (OctonionLocals.action OctonionLocals.graph v)) := by
  have hflip := twist_flip_of_realized L (twist M hf) (rootPair_realized M hf)
  have hinv (t : Fˣ) : first M hf sourceInverter * torus t *
      (first M hf sourceInverter)⁻¹ = (torus t)⁻¹ := by
    have hc : first M hf (placedCubic M t) = torus t :=
      congrArg Prod.fst (rootPair_cubic M hf t)
    have he := congrArg (first M hf)
      (sourceInverter_inverts (placedCubic M t) (placedCubic_mem_X M t))
    simpa only [map_mul, map_inv, hc] using he
  obtain ⟨t,ht⟩ := torus_inverter_coset (first M hf sourceInverter) hinv
  have hp : rootPair M hf sourceInverter = (torus t, (torus t)⁻¹) * (flip,flip) := by
    rw [rootPair_eq, ht, map_mul, twist_torus, hflip]
    rfl
  refine ⟨t, fun v => ?_⟩
  change quotientModTwoRepresentation (f (sourceInverter : Sporadic.LeechRelated.J2.Carrier))
    (L.coordinates v) = _
  rw [rootPair_action M hf, hp, map_mul, LinearEquiv.mul_apply, graph_action,
    longCubic_action]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.InverterCoset

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction

/-- The placed root J₂ inverter acts as the graph action modulo the literal
three-element long cubic, for an arbitrary additive long frame. -/
theorem rootJ2_inverter_action_coset (L : LongFrame)
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (g : LeechCentralQuotient) (hg : g ∈ centralizerI)
    (M : RootJ2SubgroupMarks L (conjugatedRootJ2 e g)) :
    ∃ t : Fˣ, ∀ v : Fin 6 → F,
      quotientModTwoRepresentation
        (conjugatedRootJ2 e g Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5.inverter)
        (L.coordinates v) =
      quotientModTwoRepresentation (longCubic L t)
        (L.coordinates (OctonionLocals.action OctonionLocals.graph v)) :=
  InverterCoset.placed_inverter_action_coset M (conjugatedRootJ2_mem e hg)

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
