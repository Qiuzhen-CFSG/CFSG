module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Assembly.Preliminary.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane.Plane.Model
/-!
# Plane movement on the whole central cover

The literal critical-pair coordinates identify the opposite vertex-core image
with a conjugate point core of symmetric six. On either whole central cover,
the transposition-fixed space lies in the point-core commutator. Pulling this
calculation through the same injective amalgam map puts the critical plane
in the moved orbit modulo the original central layer.

If the orbit centralized this plane, its full vertex-core image would make
the local critical commutator lie in the central omega subgroup, contradicting
the non-Frattini branch. These two calculations discharge the terminal
preliminary-pair premises without a hypothesis on the whole radical image.
Source: MS93 (3.6), printed p.871.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane
open LocalImages LargeDistance PlaneMovement
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)
  (o : PreliminaryPair d.radical (replacementGeometry h d))

structure PointCoordinates where
  i : d.overgroup →* FreeAmalgam d.radical
  injective : Function.Injective i
  Z0 : Subgroup d.overgroup
  Y : Subgroup d.overgroup
  Z_le : Z0 ≤ d.radical
  Y_le : Y ≤ d.radical
  map_Z : Z0.map i = Z d.radical (alpha d.radical)
  map_Y : Y.map i = Q d.radical (alpha d.radical)
  map_Q : (pCore 2 d.overgroup).map i = Q d.radical o.c
  map_W : (replacementMoved d).map i = U d.radical o.c
  map_S : (omegaCenter d.radical).map i = Z d.radical o.b
  map_R : d.radical.map i = Q d.radical o.b
  t : Equiv.Perm (Fin 6)
  swap : t.IsSwap
  g : Equiv.Perm (Fin 6)
  image_Z : Z0.map (Recognition.sourceProjection h e hz hn d) = zpowers t
  image_Y : Y.map (Recognition.sourceProjection h e hz hn d) =
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj g).toMonoidHom
  image_orbit : ((criticalOrbit d.radical o.c o.b).comap i).map
      (Recognition.sourceProjection h e hz hn d) = Y.map (Recognition.sourceProjection h e hz hn d)

namespace PointCoordinates
variable {h e hz hn d o} (s : PointCoordinates h e hz hn d o)

theorem orbit_map :
    ((criticalOrbit d.radical o.c o.b).comap s.i).map s.i =
      criticalOrbit d.radical o.c o.b := by
  apply map_comap_eq_self
  apply le_trans _ (s.map_Y ▸ map_le_range s.i s.Y)
  rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
  exact map_mono o.orbit_le_core

theorem Z_le_Y : s.Z0 ≤ s.Y := by
  apply (map_le_map_iff_of_injective s.injective).mp
  rw [s.map_Z,s.map_Y]
  exact ((replacementGeometry h d).omega_bound (alpha d.radical) rfl
    (by
      have hb : replacementDistance h d = 2 := o.distance_two
      change 0 < replacementDistance h d
      omega)).trans (omegaCenter_le _)

include s in
theorem plane_moved
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) :
    criticalPlane d.radical o.c o.b ≤
      ⁅criticalOrbit d.radical o.c o.b,stabilizer d.radical (alpha d.radical)⁆ ⊔
        Z d.radical (alpha d.radical) := by
  let := replacementMoved_normal h d
  let := moved_elementary h d
  let W := replacementMoved d
  let q := Recognition.sourceProjection h e hz hn d
  have hq := sourceProjection_surjective_of_nonfrattini h e hz hn d hb hlarge
  let hk := (Recognition.sourceProjection_kernel h e hz hn d).trans
    (moved_centralizer h e hz hn d).symm
  let ρ := NormalElementaryQuotient.representation W q hq hk
  have hmodel := moved_cover_model h e hz hn d hq
  let A0 := (criticalOrbit d.radical o.c o.b).comap s.i
  have htY : s.t ∈ Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
      (MulAut.conj s.g).toMonoidHom :=
    s.image_Y ▸ map_mono s.Z_le_Y (s.image_Z ▸ mem_zpowers s.t)
  have hfix := cover_fixed_le_pointCore_moved ρ hmodel s.g s.t htY s.swap
  have hZc : Z d.radical o.c = (W ⊔ omegaCenter d.radical).map s.i := by
    rw [Subgroup.map_sup,s.map_W,s.map_S]
    exact CentralLayer.Z_eq_moving_sup_edge_at h e hz d
      (critical_endpoint_color d.radical (alpha d.radical) rfl _ o.critical) o.adjacent_right
  intro z hzP
  have hzQ := (replacement_plane_le_intersection h e hz d hb hlarge
    o.critical o.adjacent_left o.adjacent_right hzP).2
  obtain ⟨z,hz,rfl⟩ := hZc.le (criticalPlane_le_opposite o.c o.b hzP)
  obtain ⟨w,hw,r,hr,rfl⟩ := mem_sup_of_normal_left.mp hz
  have hrC : r ∈ centralizer (s.Z0 : Set d.overgroup) := by
    intro a ha
    exact (mem_omegaCenter_iff.mp hr).2.2 a (s.Z_le ha)
  have hzC : w*r ∈ centralizer (s.Z0 : Set d.overgroup) := by
    intro a ha
    apply s.injective
    simp only [map_mul]
    simpa only [map_mul] using (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical (alpha d.radical) rfl)
      (s.map_Z ▸ mem_map_of_mem s.i ha) _ hzQ).symm
  have hwC : w ∈ centralizer (s.Z0 : Set d.overgroup) := by
    simpa only [mul_inv_cancel_right] using
      (centralizer (s.Z0 : Set d.overgroup)).mul_mem hzC
        ((centralizer (s.Z0 : Set d.overgroup)).inv_mem hrC)
  let w0 : Additive W := Additive.ofMul ⟨w,hw⟩
  have hwf : w0 ∈ fixedSpace ρ (zpowers s.t) := by
    apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
    obtain ⟨a,ha,hat⟩ := s.image_Z.ge (mem_zpowers s.t)
    rw [←hat]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [NormalElementaryQuotient.representation_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (hwC a ha)
  have hwm := hfix hwf
  rw [←s.image_Y,←s.image_orbit,←NormalElementaryQuotient.commutatorSpace_eq W q hq hk] at hwm
  have hwcomm : w ∈ ⁅W,A0⁆ := hwm
  have hwmap : s.i w ∈ ⁅criticalOrbit d.radical o.c o.b,stabilizer d.radical (alpha d.radical)⁆ := by
    have hh := mem_map_of_mem s.i hwcomm
    rw [map_commutator,s.orbit_map,commutator_comm] at hh
    apply commutator_mono le_rfl _ hh
    rw [s.map_W]
    exact (U_le_Z o.c).trans
      (critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical) rfl
        (by change 0 < replacementDistance h d; omega) o.critical)
  have hrZ : s.i r ∈ Z d.radical (alpha d.radical) := by
    have hrb : s.i r ∈ Z d.radical o.b := s.map_S ▸ mem_map_of_mem s.i hr
    have hZb : Z d.radical o.b ≤ Z d.radical (alpha d.radical) := by
      simp only [Z,show color d.radical (alpha d.radical) = false from rfl,
        DistanceTwo.NaturalCore.edge_color o.adjacent_left,Bool.true_eq_false,if_true,if_false]
      exact le_iSup_of_le o.b (le_iSup_of_le o.adjacent_left le_rfl)
    exact hZb hrb
  rw [map_mul]
  exact mul_mem_sup hwmap hrZ

include s in
theorem plane_movement
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) :
    ⁅criticalOrbit d.radical o.c o.b,criticalPlane d.radical o.c o.b⁆ ≠ ⊥ := by
  intro hzero
  have hp := replacement_radical_isPGroup h d
  have hQR := replacement_core_le_radical h d
  let A := criticalOrbit d.radical o.c o.b
  let A0 := A.comap s.i
  let q := Recognition.sourceProjection h e hz hn d
  have hYs : s.Y ≤ A0 ⊔ pCore 2 d.overgroup := by
    rw [←Recognition.sourceProjection_kernel h e hz hn d]
    exact map_le_map_iff.mp s.image_orbit.ge
  have hQa : Q d.radical (alpha d.radical) ≤ A ⊔ Q d.radical o.c := by
    have hh := map_mono (f := s.i) hYs
    rw [s.map_Y,Subgroup.map_sup,s.orbit_map,s.map_Q] at hh
    exact hh
  have hAQ : A ≤ Q d.radical (alpha d.radical) := by
    rw [Q_alpha d.radical hp hQR]
    exact map_mono o.orbit_le_core
  have hc0 := critical_endpoint_color d.radical (alpha d.radical) rfl _ o.critical
  have hZcG : Z d.radical o.c ≤ stabilizer d.radical (alpha d.radical) :=
    critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical) rfl
      (by change 0 < replacementDistance h d; omega) o.critical
  have hDplane : ⁅A,Z d.radical o.c⁆ ≤ criticalPlane d.radical o.c o.b := by
    apply le_criticalPlane_of_commutator_le _
      (le_normalizer_iff_commutator_le_right.mp
        ((hAQ.trans (DistanceTwo.NaturalCore.Q_le_endpoint_stabilizer o.adjacent_left o.adjacent_right)).trans
          (Z_normalized d.radical o.c)))
    exact (commutator_mono le_rfl
      (le_normalizer_iff_commutator_le_left.mp (hZcG.trans (criticalOrbit_normalized o.c o.b)))).trans
      (orbit_commutator_le_edge_of_transposition h e hz hn d hb hlarge
        o.critical o.adjacent_left o.adjacent_right)
  have hQcent : Q d.radical o.c ≤ centralizer (Z d.radical o.c : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical o.c hc0))
  have hinter : ⁅Q d.radical (alpha d.radical),Z d.radical o.c⁆ ≤
      criticalPlane d.radical o.c o.b := by
    apply commutator_le.mpr
    intro x hx z hz
    obtain ⟨y,hyY,rfl⟩ := s.map_Y.ge hx
    obtain ⟨a,ha,k,hk,rfl⟩ := mem_sup_of_normal_right.mp (hYs hyY)
    have hkc : Commute (s.i k) z := (hQcent (s.map_Q ▸ mem_map_of_mem s.i hk) z hz).symm
    rw [map_mul,commutatorElement_mul_left_eq_conj_mul,hkc.commutator_eq]
    simp only [mul_one,mul_inv_cancel,one_mul]
    exact hDplane (commutator_mem_commutator ha hz)
  have hcent : Q d.radical (alpha d.radical) ≤
      centralizer (criticalPlane d.radical o.c o.b : Set (FreeAmalgam d.radical)) := by
    apply hQa.trans
    apply sup_le (commutator_eq_bot_iff_le_centralizer.mp hzero)
    exact hQcent.trans (centralizer_le (criticalPlane_le_opposite o.c o.b))
  have hX : ⁅Q d.radical (alpha d.radical),Z d.radical o.c⁆ ≤ X d.radical (alpha d.radical) := by
    intro x hx
    apply mem_omegaCenter_iff.mpr
    exact ⟨DistanceTwo.NaturalCore.local_commutator_le_Q (replacementGeometry h d) hb o.critical hx,
      DistanceTwo.NaturalCore.local_commutator_pow_two (replacementGeometry h d) hb o.critical
        o.adjacent_left o.adjacent_right hx,
      le_centralizer_iff.mp hcent (hinter hx)⟩
  exact hlarge (core_le_frattini_of_critical_commutator_le_of_normal_generation
    (replacementGeometry h d) hp hQR (replacement_edge_centralizer h e hz d)
    (replacement_normal_generation h e hz d) hb o.critical (hX.trans le_sup_right))

end PointCoordinates
private theorem common_neighbor_unique
    {M : Type*} [Group M] (R : Subgroup M) {a c b b' : Vertex R}
    (hac : a ≠ c) (hab : Adjacent R a b) (hcb : Adjacent R c b)
    (hab' : Adjacent R a b') (hcb' : Adjacent R c b') : b = b' := by
  have hab0 : (cosetGraph R).Adj a b := (cosetGraph_adj R _ _).mpr hab
  have hbc0 : (cosetGraph R).Adj b c := (cosetGraph_adj R _ _).mpr (adjacent_symm R hcb)
  have hab0' : (cosetGraph R).Adj a b' := (cosetGraph_adj R _ _).mpr hab'
  have hbc0' : (cosetGraph R).Adj b' c := (cosetGraph_adj R _ _).mpr (adjacent_symm R hcb')
  let p : (cosetGraph R).Walk a c := .cons hab0 (.cons hbc0 .nil)
  let q : (cosetGraph R).Walk a c := .cons hab0' (.cons hbc0' .nil)
  have hp : p.IsPath := by simp [p,hab0.ne,hbc0.ne,hac]
  have hq : q.IsPath := by simp [q,hab0'.ne,hbc0'.ne,hac]
  have he := ((cosetGraph_isTree R).isAcyclic.subsingleton_path a c).elim
    (⟨p,hp⟩ : (cosetGraph R).Path a c) ⟨q,hq⟩
  exact congrArg (fun r : (cosetGraph R).Path a c => r.val.snd) he

include h e hz hn in
theorem pointCoordinates
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) :
    Nonempty (PointCoordinates h e hz hn d o) := by
  obtain ⟨A,Y,hAY,hYR,hAc,hYA,hne,_,_,hfix,hindex,
      b,i,hi,hAm,hab,hcb,hYm,hiW,hiS,hiL,hiR,hiQ⟩ :=
    critical_image_data_coordinates_with_edge h e hz hn d hb hlarge o.critical
  have hac : alpha d.radical ≠ o.c := by
    intro hh
    have hd := o.critical.1.trans hb
    rw [hh,SimpleGraph.dist_self] at hd
    omega
  have hbb := common_neighbor_unique d.radical hac o.adjacent_left o.adjacent_right hab hcb
  subst b
  let q := Recognition.sourceProjection h e hz hn d
  let := hAc
  have hp : IsPGroup 2 (Y.map q) :=
    ((replacement_radical_isPGroup h d).of_injective (inclusion hYR) (inclusion_injective _)).map q
  have hcent : Y.map q ≤ centralizer (A.map q : Set (Equiv.Perm (Fin 6))) := by
    rintro _ ⟨y,hy,rfl⟩ _ ⟨a,ha,rfl⟩
    exact (map_mul q a y).symm.trans ((congrArg q (hYA hy a ha)).trans (map_mul q y a))
  have hnq := critical_image_nonquadratic h e hz hn d hb hlarge o.critical
    o.adjacent_left o.adjacent_right Y i hi hYm hiW hiS
  have hnon : A.map q ≠ ⊥ := by
    intro he
    exact hne ((Recognition.sourceProjection_kernel h e hz hn d) ▸
      (Subgroup.map_eq_bot_iff A).mp he)
  obtain ⟨t,ht,ht1⟩ := (A.map q).bot_or_exists_ne_one.resolve_left hnon
  let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map _
  have hswap := isSwap_of_nonquadratic_fixer (A.map q) (Y.map q) hp
    (map_mono hAY) hcent hfix hnq ht ht1
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) t ht)
  have hcard : Nat.card (A.map q) = 2 := hindex.symm.trans
    (critical_image_two h e hz hn d hb hlarge o.critical)
  have he : A.map q = zpowers t := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr ht) ?_).symm
    rw [hcard,Nat.card_zpowers,hswap.orderOf]
  obtain ⟨g,hg⟩ := critical_core_image_pointCore h e hz hn d hb hlarge o Y hYR i hi hYm hiQ hiW hiS
  let sm : ImageModel o := {
    projection := q
    kernel := Recognition.sourceProjection_kernel h e hz hn d
    component_image := Recognition.sourceProjection_component h e hz hn d }
  let A0 := (criticalOrbit d.radical o.c o.b).comap i
  have hAQ : criticalOrbit d.radical o.c o.b ≤ Q d.radical (alpha d.radical) := by
    rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
    exact map_mono o.orbit_le_core
  have hA0m : A0.map i = criticalOrbit d.radical o.c o.b := map_comap_eq_self
    (hAQ.trans (hYm ▸ map_le_range i Y))
  have hA0Y : A0 ≤ Y := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [hA0m,hYm]
    exact hAQ
  let := o.quotient_elementary
  have h8 : Nat.card (A0.map q) = 8 := by
    rw [←relIndex_ker,Recognition.sourceProjection_kernel]
    have hh := relIndex_map_map_of_injective (pCore 2 d.overgroup) A0 hi
    rw [hiQ,hA0m] at hh
    rw [←hh]
    exact (sm.strict_indices (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)).2.1
  have hY8 : Nat.card (Y.map q) = 8 := by
    rw [hg,card_map_of_injective (MulAut.conj g).injective]
    exact Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore_card
  have hEq : A0.map q = Y.map q := eq_of_le_of_card_ge (map_mono hA0Y) (by omega)
  exact ⟨{
    i := i
    injective := hi
    Z0 := A
    Y := Y
    Z_le := hAY.trans hYR
    Y_le := hYR
    map_Z := hAm
    map_Y := hYm
    map_Q := hiQ
    map_W := hiW
    map_S := hiS
    map_R := hiR
    t := t
    swap := hswap
    g := g
    image_Z := he
    image_Y := hg
    image_orbit := hEq }⟩

include h e hz hn o in
theorem false_of_preliminary_nonfrattini
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) : False := by
  obtain ⟨s⟩ := pointCoordinates h e hz hn d o hb hlarge
  exact false_of_preliminary_plane_calculations h e hz hn d hb hlarge o
    (s.plane_moved hb hlarge) (s.plane_movement hb hlarge)

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
