module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Noncentral.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Selection.BaseEdge
/-!
# Favorable critical orbits before maximal-plane equality

Select a minimum image index at the literal base edge and reverse that
critical pair. The original orbit containment, edge commutator and critical
index calculations give both comparison inequalities. The new source
noncentrality theorem makes the generating plane escape its fixed preimage.

This interface omits the whole-core movement identity from OrderedOrbit:
that identity follows later from plane equality and cannot justify the
earlier selection. Existing public structures are preserved.
Adapted from Geometry.Selection, Selection.BaseEdge and PairEstimates.Data.
Source: MS93 (3.6), printed p.871.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} (geo : Geometry R)

structure LocalData : Prop where
  edge_centralizer : EdgeCentralizerCondition R
  orbit_core : ∀ c b,
    CriticalPair R (alpha R) c (geo.exists_critical _ rfl) →
    Adjacent R (alpha R) b → Adjacent R c b →
    criticalOrbitNative R c b ≤ pCore 2 M
  commutator_edge : ∀ c b,
    CriticalPair R (alpha R) c (geo.exists_critical _ rfl) →
    Adjacent R (alpha R) b → Adjacent R c b →
    ⁅Q R (alpha R),criticalOrbit R c b⁆ ≤ Z R b
  image_two : ∀ c,
    CriticalPair R (alpha R) c (geo.exists_critical _ rfl) →
    (Q R c).relIndex (Z R (alpha R)) = 2
  plane_not_fixed : ∀ c b,
    CriticalPair R (alpha R) c (geo.exists_critical _ rfl) →
    Adjacent R (alpha R) b → Adjacent R c b →
    ¬ (criticalPlane R c b).comap (embedM R) ≤ orbitFixedKernel (pResidual 2 M) R c b

theorem exists_reversed_critical_coordinates
    (hl : LocalData geo) (hb : geo.b R = 2)
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


structure PreliminaryPair (R : Subgroup M) (geo : Geometry R) where
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
  strict_index :
    2 * (commutatorPreimage (criticalOrbit R c b) opposite (Z R (alpha R))).relIndex
      (criticalOrbit R c b) ≤ (Q R c).relIndex (criticalOrbit R c b)
  ordered_index : (Q R c).relIndex (criticalOrbit R c b) ≤ (Q R (alpha R)).relIndex opposite

  distance_two : geo.b R = 2
  orbit_le_core : criticalOrbitNative R c b ≤ pCore 2 M
  layer_le : orbitLayer R ≤ criticalOrbitNative R c b
  commutator_le_layer : ⁅pCore 2 M,criticalOrbitNative R c b⁆ ≤ orbitLayer R
  plane_not_fixed : ¬ (criticalPlane R c b).comap (embedM R) ≤
    orbitFixedKernel (pResidual 2 M) R c b

theorem strict_index (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hl : LocalData geo) (hb : geo.b R = 2) {c b : Vertex R}
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

namespace PreliminaryPair
variable {geo} (o : PreliminaryPair R geo)

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

end PreliminaryPair

theorem exists_preliminaryPair_base (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hl : LocalData geo) (hb : geo.b R = 2) : ∃ o : PreliminaryPair R geo, o.b = beta R := by
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
    strict_index := strict_index geo hp hQR hl hb hc hab hcb B hBQ hBcomm
    ordered_index := ?_
    distance_two := hb
    orbit_le_core := hl.orbit_core _ _ hc hab hcb
    layer_le := layer_le_orbit geo hb hc hab hcb
    commutator_le_layer := orbit_commutator_le_layer geo hp hQR hb hc hab hcb
    plane_not_fixed := hl.plane_not_fixed _ _ hc hab hcb },hbeta⟩
  · rw [←hSa]
    exact (map_mono (criticalOrbit_normalized (R := R) d (beta R))).trans (le_normalizer_map i)
  · change _ ≤ (Q R (alpha R)).relIndex ((criticalOrbit R d (beta R)).map i)
    rw [←hQd,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact Function.argmin_le f ⟨(d,beta R),hd,hbase,hdb,rfl⟩

universe u
theorem source_localData {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) :
    LocalData (replacementGeometry h d) where
  edge_centralizer := replacement_edge_centralizer h e hz d
  orbit_core := fun _ _ hc hab hcb => replacement_orbit_le_core h e hz d hb hlarge hc hab hcb
  commutator_edge := fun _ _ hc hab hcb =>
    orbit_commutator_le_edge_of_transposition h e hz hn d hb hlarge hc hab hcb
  image_two := fun _ hc => LocalImages.critical_image_two h e hz hn d hb hlarge hc
  plane_not_fixed := fun _ _ hc hab hcb =>
    Noncentral.critical_plane_not_fixed h e hz hn d hb hlarge hc hab hcb

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
