module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Contracts
public import Mathlib.Order.WellFounded

/-!
# Selecting and rebasing the favorable pair of actual critical orbits

Minimize the orbit image index, reverse the selected critical pair, and
conjugate its native orbit back along the common edge. The resulting opposite
orbit retains its literal conjugation witness. The transverse Z-layer of
index two gives the strict fixed-index inequality for this same pair.

Adapted from Chapter C's SymplecticDistanceTwo/OrbitPair, OrbitChoice and
OrbitComparison, using explicit local identities on the original carrier.
Source: MS93 (3.6), printed p.871.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} (geo : Geometry R)

/-- Rebase the reversed critical pair at its specified common edge. -/
theorem exists_reversed_critical_coordinates
    (hl : LocalCalculations R geo) (hb : geo.b R = 2)
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    ∃ (g : FreeAmalgam R) (d : Vertex R),
      act R g (alpha R) = c ∧ act R g d = alpha R ∧ act R g (beta R) = b ∧
      CriticalPair R (alpha R) d (geo.exists_critical (alpha R) rfl) ∧
      Adjacent R d (beta R) := by
  have hc0 := critical_endpoint_color R (alpha R) rfl _ hc
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common R c b).mp hcb
  · rcases hg with ⟨rfl,rfl⟩
    let d := act R g⁻¹ (alpha R)
    have hga : act R g (alpha R) = mVertex R g := by simp [alpha]
    have hgb : act R g (beta R) = hVertex R g := by simp [beta]
    have hgd : act R g d = alpha R := by
      dsimp only [d]
      rw [←act_mul,inv_mul_cancel,act_one]
    have hback : act R g⁻¹ (mVertex R g) = alpha R := by simp [alpha]
    have hrev := critical_reverse R geo hl.edge_centralizer
      (alpha R) rfl (by change 0 < geo.b R; omega) (mVertex R g) hc0 hc
    have he : ∃n, CriticalRadius R (act R g⁻¹ (mVertex R g)) n := by
      rw [hback]
      exact geo.exists_critical (alpha R) rfl
    have hcrit := (criticalPair_act_iff R g⁻¹ (mVertex R g) (alpha R)
      (geo.exists_critical (mVertex R g) hc0) he).mpr hrev
    have hcrit' : CriticalPair R (alpha R) d (geo.exists_critical (alpha R) rfl) := by
      simpa only [hback] using hcrit
    refine ⟨g,d,hga,hgd,hgb,hcrit',?_⟩
    have hh := (adjacent_act_iff R g d (beta R)).mp
      (by rw [hgd,hgb];exact hab)
    exact hh
  · rw [hg.1] at hc0
    cases hc0


/-- All retained markings concern one selected literal opposite orbit. -/
structure OrderedOrbit where
  c : Vertex R
  b : Vertex R
  opposite : Subgroup (FreeAmalgam R)
  critical : CriticalPair R (alpha R) c (geo.exists_critical _ rfl)
  adjacent_left : Adjacent R (alpha R) b
  adjacent_right : Adjacent R c b
  rebased : RebasedOrbit R geo c b opposite
  opposite_le : opposite ≤ Q R c
  opposite_normalized : stabilizer R c ≤ normalizer (opposite : Set (FreeAmalgam R))
  opposite_commutator : ⁅Q R c,opposite⁆ ≤ Z R b
  opposite_movement : ⁅opposite,Ltilde R c⁆ = core R c
  strict_index :
    2 * (commutatorPreimage (criticalOrbit R c b) opposite (Z R (alpha R))).relIndex
      (criticalOrbit R c b) ≤ (Q R c).relIndex (criticalOrbit R c b)
  ordered_index : (Q R c).relIndex (criticalOrbit R c b) ≤ (Q R (alpha R)).relIndex opposite

/-- The index-two transverse layer gives the strict inequality without a
point-core coordinate map or a natural subgroup. -/
theorem strict_index (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hl : LocalCalculations R geo) (hb : geo.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical _ rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (B : Subgroup (FreeAmalgam R)) (hBQ : B ≤ Q R c) (hBcomm : ⁅Q R c,B⁆ ≤ Z R b) :
    2 * (commutatorPreimage (criticalOrbit R c b) B (Z R (alpha R))).relIndex
      (criticalOrbit R c b) ≤ (Q R c).relIndex (criticalOrbit R c b) := by
  let A := criticalOrbit R c b
  have hAQ : A ≤ Q R (alpha R) := by
    rw [Q_alpha R hp hQR]
    exact map_mono (hl.orbit_core c b hc hab hcb)
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite A := Finite.of_injective
    (inclusion (hAQ.trans (show Q R (alpha R) ≤ stabilizer R (alpha R) from fun _ hx => hx.1)))
    (inclusion_injective _)
  have hZb : Z R b ≤ Z R (alpha R) := by
    simp only [Z,show color R (alpha R) = false from rfl,edge_color hab,
      Bool.true_eq_false,if_true,if_false]
    exact le_iSup_of_le b (le_iSup_of_le hab le_rfl)
  have hAC : A ≤ normalizer (Q R c : Set (FreeAmalgam R)) :=
    (hAQ.trans (Q_le_endpoint_stabilizer hab hcb)).trans (Q_normalized R c)
  have hCZ : ⁅A ⊓ Q R c,B⁆ ≤ Z R (alpha R) :=
    ((commutator_mono inf_le_right le_rfl).trans hBcomm).trans hZb
  have hZB : ⁅Z R (alpha R),B⁆ ≤ Z R (alpha R) :=
    le_normalizer_iff_commutator_le_left.mp
      ((hBQ.trans ((Q_le_adjacent_h R (edge_color hab) hcb).trans
        (fun _ hx => hx.2 _ (adjacent_symm R hab)))).trans (Z_normalized R (alpha R)))
  have hh := commutatorPreimage_relIndex_mul_le A B (Q R c) (Z R (alpha R))
    (Z_le_criticalOrbit geo hb hc hab hcb) hAC hCZ hZB
  rwa [hl.image_two c hc] at hh

/-- Choose a minimal orbit image and retain the actual reversed-orbit
witness as well as both inequalities. -/
theorem exists_orderedOrbit (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hl : LocalCalculations R geo) (hb : geo.b R = 2) : Nonempty (OrderedOrbit geo) := by
  let P := {p : Vertex R × Vertex R //
    CriticalPair R (alpha R) p.1 (geo.exists_critical _ rfl) ∧
    Adjacent R (alpha R) p.2 ∧ Adjacent R p.1 p.2}
  have : Nonempty P := by
    obtain ⟨c,b,hc,hab,hcb⟩ := critical_edge_exists geo hb
    exact ⟨⟨(c,b),hc,hab,hcb⟩⟩
  let f : P → ℕ := fun p => (Q R p.val.1).relIndex (criticalOrbit R p.val.1 p.val.2)
  let p := Function.argmin f
  obtain ⟨hc,hab,hcb⟩ := p.property
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
    ordered_index := ?_ }⟩
  · rw [←hSa]
    exact (map_mono (criticalOrbit_normalized (R := R) d (beta R))).trans (le_normalizer_map i)
  · have hh := congrArg (Subgroup.map i) (hl.commutator_core d (beta R) hd hbase hdb)
    rwa [map_commutator,hLa,hCa] at hh
  · change _ ≤ (Q R (alpha R)).relIndex ((criticalOrbit R d (beta R)).map i)
    rw [←hQd,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact Function.argmin_le f ⟨(d,beta R),hd,hbase,hdb⟩

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
