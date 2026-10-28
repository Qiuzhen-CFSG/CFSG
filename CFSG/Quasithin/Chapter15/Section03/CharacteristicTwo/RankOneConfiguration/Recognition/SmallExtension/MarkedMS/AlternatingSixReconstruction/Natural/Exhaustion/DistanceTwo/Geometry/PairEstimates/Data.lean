module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Selection

/-!
# Local orbit data before the paired estimates

The reversed orbit retains its literal conjugation witness. Local calculations
supply its normalization and movement, and make the base orbit quotient
elementary with nontrivial component action. None of the three paired estimates
is used here. This separates the strict-index argument from the later plane
and central-attachment calculations in MS93 (3.6), printed p.871.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} {geo : Geometry R}

/-- The actual pair before full edge image, plane movement, or elementary
paired commutators have been established. -/
structure EarlyPair (R : Subgroup M) (geo : Geometry R) extends OrderedOrbit geo where
  distance_two : geo.b R = 2
  orbit_le_core : criticalOrbitNative R c b ≤ pCore 2 M
  layer_le : orbitLayer R ≤ criticalOrbitNative R c b
  commutator_le_layer : ⁅pCore 2 M,criticalOrbitNative R c b⁆ ≤ orbitLayer R
  plane_not_fixed : ¬ (criticalPlane R c b).comap (embedM R) ≤
    orbitFixedKernel (pResidual 2 M) R c b

namespace EarlyPair
variable (o : EarlyPair R geo)

theorem plane_elementary : IsElementaryAbelian 2 (criticalPlane R o.c o.b) := by
  have hc := critical_endpoint_color R (alpha R) rfl _ o.critical
  have hpos : 0 < criticalDistance R o.c (geo.exists_critical o.c hc) := by
    rw [geo.distance_constant o.c hc]
    change 0 < geo.b R
    rw [o.distance_two]
    decide
  let := Z_elementary_of_positive R geo o.c hc hpos
  exact IsElementaryAbelian.of_le ((closure_le _).mpr (fun _ hx => hx.1))

/-- Only the quotient by the entire base Z-layer is made elementary. -/
theorem quotient_elementary : IsElementaryAbelian 2 (OrbitQuotient R o.c o.b) := by
  let A := criticalOrbitNative R o.c o.b
  let Y := (criticalPlane R o.c o.b).comap (embedM R)
  let := o.plane_elementary
  let := IsElementaryAbelian.comap_of_injective (p := 2) (embedM R) (embedM_injective R)
    (criticalPlane R o.c o.b)
  have hab : IsMulCommutative (OrbitQuotient R o.c o.b) := by
    apply Normal.quotient_commutative_iff_commutator_le.mpr
    have hh : ⁅A,A⁆ ≤ orbitLayer R :=
      (commutator_mono o.orbit_le_core le_rfl).trans o.commutator_le_layer
    intro a ha
    apply hh
    rw [←map_subtype_commutator]
    exact mem_map_of_mem A.subtype ha
  change IsElementaryAbelian 2 (normalClosure (Y : Set M) ⧸
    (orbitLayer R).subgroupOf (normalClosure (Y : Set M)))
  exact normalClosure_quotient_elementary 2 Y _ hab

/-- The opposite orbit lies in the literal base vertex carrier. -/
theorem opposite_map : (o.opposite.comap (embedM R)).map (embedM R) = o.opposite := by
  apply map_comap_eq_self
  apply le_trans _ (stabilizer_m_base R).le
  exact (o.opposite_le.trans
    (Q_le_adjacent_h R (DistanceTwo.NaturalCore.edge_color o.adjacent_left)
      o.adjacent_right)).trans (fun _ hx => hx.2 _ (adjacent_symm R o.adjacent_left))

end EarlyPair

/-- Local calculations supply all data needed for faithful orbit actions for
every ordered literal pair, before proving any paired estimate. -/
def earlyPair (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hl : LocalCalculations R geo) (hb : geo.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    (o : OrderedOrbit geo) : EarlyPair R geo where
  toOrderedOrbit := o
  distance_two := hb
  orbit_le_core := hl.orbit_core o.c o.b o.critical o.adjacent_left o.adjacent_right
  layer_le := layer_le_orbit geo hb o.critical o.adjacent_left o.adjacent_right
  commutator_le_layer := orbit_commutator_le_layer geo hp hQR hb
    o.critical o.adjacent_left o.adjacent_right
  plane_not_fixed := by
    apply plane_not_fixed_of_movement
    intro hm
    have hh := map_mono (f := embedM R) hm
    rw [map_commutator,←Ltilde_alpha] at hh
    change ⁅criticalOrbit R o.c o.b,Ltilde R (alpha R)⁆ ≤ _ at hh
    rw [hl.commutator_core o.c o.b o.critical o.adjacent_left o.adjacent_right] at hh
    have hZ : Z R (alpha R) ≤ X R (alpha R) :=
      geo.omega_bound (alpha R) rfl (by change 0 < geo.b R; omega)
    exact hlarge (((hh.trans (map_comap_le _ _)).trans hZ).trans le_sup_right)

/-- Reconstruct the ordered data for the specified B, retaining its exact
reversed/rebased witness and both supplied relative-index inequalities. -/
def orderedOfRebased (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hl : LocalCalculations R geo) (c b : Vertex R)
    (B : Subgroup (FreeAmalgam R))
    (hc : CriticalPair R (alpha R) c (geo.exists_critical _ rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hr : RebasedOrbit R geo c b B)
    (hs : 2 * (commutatorPreimage (criticalOrbit R c b) B (Z R (alpha R))).relIndex
      (criticalOrbit R c b) ≤ (Q R c).relIndex (criticalOrbit R c b))
    (ho : (Q R c).relIndex (criticalOrbit R c b) ≤ (Q R (alpha R)).relIndex B) :
    OrderedOrbit geo := by
  have hh : B ≤ Q R c ∧ stabilizer R c ≤ normalizer (B : Set (FreeAmalgam R)) ∧
      ⁅Q R c,B⁆ ≤ Z R b ∧ ⁅B,Ltilde R c⁆ = core R c := by
    obtain ⟨g,d,hga,hgd,hgb,hd,hdb,hB⟩ := hr
    let i := (MulAut.conj g⁻¹).toMonoidHom
    have hQa : (Q R (alpha R)).map i = Q R c := by rw [←Q_act,hga]
    have hZb : (Z R (beta R)).map i = Z R b := by rw [←Z_act,hgb]
    have hLa : (Ltilde R (alpha R)).map i = Ltilde R c := by rw [←Ltilde_act,hga]
    have hCa : (core R (alpha R)).map i = core R c := by rw [←core_act,hga]
    have hSa : (stabilizer R (alpha R)).map i = stabilizer R c := by rw [←stabilizer_act,hga]
    refine ⟨?_,?_,?_,?_⟩
    · rw [hB,←hQa,Q_alpha R hp hQR]
      exact map_mono (map_mono (hl.orbit_core d (beta R) hd (base_adjacent R) hdb))
    · rw [hB,←hSa]
      exact (map_mono (criticalOrbit_normalized (R := R) d (beta R))).trans
        (le_normalizer_map i)
    · have hh := map_mono (f := i) (hl.commutator_edge d (beta R) hd (base_adjacent R) hdb)
      rwa [map_commutator,hQa,hZb,←hB] at hh
    · have hh := congrArg (Subgroup.map i) (hl.commutator_core d (beta R) hd (base_adjacent R) hdb)
      rwa [map_commutator,hLa,hCa,←hB] at hh
  exact {
    c := c, b := b, opposite := B
    critical := hc, adjacent_left := hab, adjacent_right := hcb
    rebased := hr
    opposite_le := hh.1
    opposite_normalized := hh.2.1
    opposite_commutator := hh.2.2.1
    opposite_movement := hh.2.2.2
    strict_index := hs, ordered_index := ho }

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
