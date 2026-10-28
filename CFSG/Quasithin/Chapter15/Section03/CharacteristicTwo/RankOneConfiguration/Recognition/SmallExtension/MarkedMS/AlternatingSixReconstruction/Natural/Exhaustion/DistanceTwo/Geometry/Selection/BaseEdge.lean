module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Selection
/-!
# A favorable paired orbit at the literal base edge

Minimize the same source image index among critical pairs whose common edge
is beta. Critical reversal and rebasing keep that set nonempty and preserve
the minimization comparison. The returned OrderedOrbit has all original
fields and its edge is literally beta, allowing its full quotient image
to pull back to the unchanged replacement radical.

Adapted from Geometry.Selection; source: MS93 (3.6), printed p.871.
-/

public noncomputable section
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} (geo : Geometry R)
theorem exists_orderedOrbit_base (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hl : LocalCalculations R geo) (hb : geo.b R = 2) : ∃ o : OrderedOrbit geo, o.b = beta R := by
  let P := {p : Vertex R × Vertex R //
    CriticalPair R (alpha R) p.1 (geo.exists_critical _ rfl) ∧
    Adjacent R (alpha R) p.2 ∧ Adjacent R p.1 p.2 ∧ p.2 = beta R}
  have : Nonempty P := by
    obtain ⟨c,b,hc,hab,hcb⟩ := critical_edge_exists geo hb
    obtain ⟨g,d,hga,hgd,hgb,hd,hdb⟩ := exists_reversed_critical_coordinates geo hl hb hc hab hcb
    exact ⟨⟨(d,beta R),hd,base_adjacent R,hdb,rfl⟩⟩
  let f : P → ℕ := fun p => (Q R p.val.1).relIndex (criticalOrbit R p.val.1 p.val.2)
  let p := Function.argmin f
  obtain ⟨hc,hab,hcb,hbeta⟩ := p.property
  obtain ⟨g,d,hga,hgd,hgb,hd,hdb⟩ := exists_reversed_critical_coordinates geo hl hb hc hab hcb
  let i := (MulAut.conj g⁻¹).toMonoidHom
  let B := (criticalOrbit R d (beta R)).map i
  have hbase := base_adjacent R
  have hQa : (Q R (alpha R)).map i = Q R p.val.1 := by rw [←Q_act,hga]
  have hQd : (Q R d).map i = Q R (alpha R) := by rw [←Q_act,hgd]
  have hZb : (Z R (beta R)).map i = Z R p.val.2 := by rw [←Z_act,hgb]
  have hLa : (Ltilde R (alpha R)).map i = Ltilde R p.val.1 := by rw [←Ltilde_act,hga]
  have hCa : (core R (alpha R)).map i = core R p.val.1 := by rw [←core_act,hga]
  have hSa : (stabilizer R (alpha R)).map i = stabilizer R p.val.1 := by rw [←stabilizer_act,hga]
  have hBQ : B ≤ Q R p.val.1 := by
    rw [←hQa,Q_alpha R hp hQR]
    exact map_mono (map_mono (hl.orbit_core d (beta R) hd hbase hdb))
  have hBcomm : ⁅Q R p.val.1,B⁆ ≤ Z R p.val.2 := by
    have hh := map_mono (f := i) (hl.commutator_edge d (beta R) hd hbase hdb)
    rwa [map_commutator,hQa,hZb] at hh
  refine ⟨{
    c := p.val.1, b := p.val.2, opposite := B
    critical := hc, adjacent_left := hab, adjacent_right := hcb
    rebased := ⟨g,d,hga,hgd,hgb,hd,hdb,rfl⟩
    opposite_le := hBQ
    opposite_normalized := ?_
    opposite_commutator := hBcomm
    opposite_movement := ?_
    strict_index := strict_index geo hp hQR hl hb hc hab hcb B hBQ hBcomm
    ordered_index := ?_ },hbeta⟩
  · rw [←hSa]
    exact (map_mono (criticalOrbit_normalized (R := R) d (beta R))).trans (le_normalizer_map i)
  · have hh := congrArg (Subgroup.map i) (hl.commutator_core d (beta R) hd hbase hdb)
    rwa [map_commutator,hLa,hCa] at hh
  · change _ ≤ (Q R (alpha R)).relIndex ((criticalOrbit R d (beta R)).map i)
    rw [←hQd,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact Function.argmin_le f ⟨(d,beta R),hd,hbase,hdb,rfl⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry
