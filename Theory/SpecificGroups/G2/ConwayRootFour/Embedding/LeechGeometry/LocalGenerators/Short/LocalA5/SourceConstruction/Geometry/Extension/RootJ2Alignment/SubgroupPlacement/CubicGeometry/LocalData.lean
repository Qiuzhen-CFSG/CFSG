module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.FixedVectors

/-!
# Reduction of long-cubic geometry to intrinsic Leech model facts

The long cubic has order three and no nonzero fixed vector on the whole
binary Leech module. A relative fusion theorem for such cubics therefore
places it in the root J₂, once the marked root element is identified as
fixed-free. Conjugation inside C(I) transports the literal common
centralizers. An upper bound by the order of SL₃(4) then forces equality
with the already faithful long subgroup.

The relative-fusion theorem, the root element's fixed-vector calculation,
and its ambient centralizer bound remain explicit. The carrier equivalence
only transports the root element and its order. No class identification or
centralizer bound is inferred from that equivalence.

The final theorem supplies precisely both inputs of
`exists_rootJ2SubgroupMarks_of_cubic_local_data`. Their application to that
consumer is in `CubicGeometry.PlacementApplication`.

Source: Aschbacher, *Sporadic Groups* (1994), 49.1–49.2, p.280,
and the proof of 49.5, pp.283–284. In particular 49.2 identifies the
full C_G(IX) with SL₃(4); 48.8 concerns the Suzuki five-local calculation.
-/

@[expose] public noncomputable section

open Matrix Atlas.Conway Atlas.Codes Atlas.Lattices
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
open OctonionLocals
/-- Absence of nonzero fixed vectors in the actual binary Leech module. -/
def CubicFixedFree (a : LeechCentralQuotient) : Prop :=
  ∀ v : LeechModTwo, quotientModTwoRepresentation a v = v → v = 0

/-- The marked root cubic element, before ambient conjugation. -/
def rootJ2Cubic (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel) :
    LeechCentralQuotient :=
  icosianProjectiveToCo1 (e Sporadic.LeechRelated.J2.RecognitionGeometry.x)

theorem rootJ2Cubic_mem (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel) :
    rootJ2Cubic e ∈ centralizerI := janko_mem_centralizerI _

theorem rootJ2Cubic_order (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel) :
    orderOf (rootJ2Cubic e) = 3 := by
  rw [rootJ2Cubic, orderOf_injective icosianProjectiveToCo1 icosianProjectiveToCo1_injective,
    e.orderOf_eq]
  exact Sporadic.LeechRelated.J2.RecognitionGeometry.orderOf_x

theorem rootJ2Cubic_map (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (g : LeechCentralQuotient) :
    Sporadic.LeechRelated.J2.RecognitionGeometry.X.map (conjugatedRootJ2 e g) =
      (Subgroup.zpowers (rootJ2Cubic e)).map (MulAut.conj g).toMonoidHom := by
  rw [Sporadic.LeechRelated.J2.RecognitionGeometry.X, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers]
  rfl

/-- An intrinsic relative-fusion statement, independent of any long frame or J₂ marking. -/
def FixedFreeCubicFusion : Prop :=
  ∀ a b : LeechCentralQuotient, a ∈ centralizerI → b ∈ centralizerI →
    orderOf a = 3 → orderOf b = 3 → CubicFixedFree a → CubicFixedFree b →
    ∃ g ∈ centralizerI,
      Subgroup.zpowers a = (Subgroup.zpowers b).map (MulAut.conj g).toMonoidHom

private theorem exists_nonidentity_scalar : ∃ t : Fˣ, t ≠ 1 := by
  have hc : Nat.card Fˣ = 3 := by
    rw [Nat.card_units, GaloisField.card 2 2 (by decide)]
    norm_num
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp (by rw [hc]; decide)
  exact exists_ne 1

theorem exists_rootJ2CubicMark_of_fixedFree_fusion (L : LongFrame)
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (hfusion : FixedFreeCubicFusion) (hroot : CubicFixedFree (rootJ2Cubic e)) :
    ∃ g ∈ centralizerI, (longCubic L).range ≤
      Sporadic.LeechRelated.J2.RecognitionGeometry.X.map (conjugatedRootJ2 e g) := by
  obtain ⟨t, ht⟩ := exists_nonidentity_scalar
  obtain ⟨g, hg, hmark⟩ := hfusion (longCubic L t) (rootJ2Cubic e)
    (L.long_mem _) (rootJ2Cubic_mem e) (longCubic_order L ht) (rootJ2Cubic_order e)
    (longCubic_fixed_eq_zero L ht) hroot
  refine ⟨g, hg, ?_⟩
  rw [rootJ2Cubic_map, longCubic_range_eq_zpowers L ht, hmark]

theorem longFrame_range_card (L : LongFrame) :
    Nat.card L.long.range = Nat.card SL(3,F) :=
  (Nat.card_congr (MonoidHom.ofInjective (longFrame_long_injective L)).toEquiv).symm

private theorem cubicCentralizer_map_conj (P : Subgroup LeechCentralQuotient)
    {g : LeechCentralQuotient} (hg : g ∈ centralizerI) :
    (centralizerI ⊓ Subgroup.centralizer (P : Set LeechCentralQuotient)).map
        (MulAut.conj g).toMonoidHom =
      centralizerI ⊓ Subgroup.centralizer
        (P.map (MulAut.conj g).toMonoidHom : Set LeechCentralQuotient) := by
  apply le_antisymm
  · rintro _ ⟨a, ⟨haI, haP⟩, rfl⟩
    refine ⟨centralizerI.mul_mem (centralizerI.mul_mem hg haI) (centralizerI.inv_mem hg), ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    exact (MulAut.conj g).map_mul b a ▸ (MulAut.conj g).map_mul a b ▸
      congrArg (MulAut.conj g) (haP b hb)
  · rintro a ⟨haI, haP⟩
    refine ⟨(MulAut.conj g).symm a, ⟨?_, ?_⟩, (MulAut.conj g).apply_symm_apply a⟩
    · exact centralizerI.mul_mem
        (centralizerI.mul_mem (centralizerI.inv_mem hg) haI) hg
    · intro b hb
      apply (MulAut.conj g).injective
      rw [map_mul, map_mul, (MulAut.conj g).apply_symm_apply]
      exact haP _ ⟨b, hb, rfl⟩

theorem cubicCentralizer_card_conjugate (P : Subgroup LeechCentralQuotient)
    {g : LeechCentralQuotient} (hg : g ∈ centralizerI) :
    Nat.card ↥(centralizerI ⊓ Subgroup.centralizer
      (P.map (MulAut.conj g).toMonoidHom : Set LeechCentralQuotient)) =
      Nat.card ↥(centralizerI ⊓ Subgroup.centralizer (P : Set LeechCentralQuotient)) := by
  rw [← cubicCentralizer_map_conj P hg]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

/-- A bound on the unconjugated root cubic suffices for the literal long centralizer. -/
theorem rootJ2_cubicCentralizer_le_long_of_root_bound (L : LongFrame)
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (hmark : ∃ g ∈ centralizerI, (longCubic L).range ≤
      Sporadic.LeechRelated.J2.RecognitionGeometry.X.map (conjugatedRootJ2 e g))
    (hbound : Nat.card ↥(centralizerI ⊓ Subgroup.centralizer
      (Subgroup.zpowers (rootJ2Cubic e) : Set LeechCentralQuotient)) ≤ Nat.card SL(3,F)) :
    centralizerI ⊓ Subgroup.centralizer ((longCubic L).range : Set LeechCentralQuotient) ≤
      L.long.range := by
  obtain ⟨g, hg, hmark⟩ := hmark
  have heq : (longCubic L).range =
      Sporadic.LeechRelated.J2.RecognitionGeometry.X.map (conjugatedRootJ2 e g) := by
    apply Subgroup.eq_of_le_of_card_ge hmark
    rw [Subgroup.card_map_of_injective (conjugatedRootJ2_injective e g),
      Sporadic.LeechRelated.J2.RecognitionGeometry.card_X, longCubic_card]
  have hc : Nat.card ↥(centralizerI ⊓ Subgroup.centralizer
      ((longCubic L).range : Set LeechCentralQuotient)) ≤ Nat.card L.long.range := by
    rw [heq, rootJ2Cubic_map, cubicCentralizer_card_conjugate _ hg, longFrame_range_card]
    exact hbound
  exact (Subgroup.eq_of_le_of_card_ge (longFrame_range_le_cubicCentralizer L) hc).ge

/-- Conditional assembly of both ambient inputs consumed by `SubgroupPlacement`. -/
theorem rootJ2_cubicGeometry_of_fixedFree_local_data (L : LongFrame)
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (hfusion : FixedFreeCubicFusion) (hroot : CubicFixedFree (rootJ2Cubic e))
    (hbound : Nat.card ↥(centralizerI ⊓ Subgroup.centralizer
      (Subgroup.zpowers (rootJ2Cubic e) : Set LeechCentralQuotient)) ≤ Nat.card SL(3,F)) :
    (∃ g ∈ centralizerI, (longCubic L).range ≤
      Sporadic.LeechRelated.J2.RecognitionGeometry.X.map (conjugatedRootJ2 e g)) ∧
    centralizerI ⊓ Subgroup.centralizer ((longCubic L).range : Set LeechCentralQuotient) ≤
      L.long.range := by
  have hmark := exists_rootJ2CubicMark_of_fixedFree_fusion L e hfusion hroot
  exact ⟨hmark, rootJ2_cubicCentralizer_le_long_of_root_bound L e hmark hbound⟩

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
