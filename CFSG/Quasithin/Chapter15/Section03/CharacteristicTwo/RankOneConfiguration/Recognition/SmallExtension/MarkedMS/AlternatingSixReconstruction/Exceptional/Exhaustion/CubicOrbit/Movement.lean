module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.CubicOrbit.Bounds
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition.FromModel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane.Vertex.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane.Plane.Model
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane.Recognition.Source

/-!
# Whole movement of the favorable cubic critical-plane orbit

The exact order-eight indices identify the opposite vertex-core image with
an actual point core of symmetric six. On the reversed source pair, the
whole moved cover and the original edge layer give coordinates retaining
the initial cubic kernel. The transposition-fixed hyperplane lies in the
point-core commutator, so the critical plane is moved modulo the base layer.
Normal generation then proves full component movement of the entire orbit,
and the three-subgroups argument makes its literal fixed preimage central.

Equality of two-subgroup images lifts modulo Q, even though the projection
has the larger kernel E: the intersection of a two-subgroup with E lies in Q.
This supplies the opposite-core supplement without discarding E/Q. If the
orbit centralized its generating plane, the resulting critical commutator
would lie in the central omega layer, contradicting the cubic initial kernel.
Thus recognition of the fixed quotient alone suffices for the terminal
involution contradiction. No separate intersection-bound premise remains
in this route. CubicOrbit.Source applies it to the whole original blockU
and literal rank-two consumer. Quotient recognition, larger distances and
final reconstruction remain with this reconstruction owner.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871;
Aschbacher--Smith C.1.31--32, pp.135--136. The point-core calculation is
reused from Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane.Plane.Model.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation BinaryPermutation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction
open Natural.Exhaustion.DistanceTwo.Geometry
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "T" => edge L R
local notation "W" => (⁅centralOmega L R,K⁆ : Subgroup M)
local notation "π" => projection h e hz hk


include h e hz hk in
/-- The odd extension kernel does not alter the index of any two-subgroup. -/
theorem permutation_image_card_of_two (A : Subgroup M) (hA : IsPGroup 2 A) :
    Nat.card (A.map π) = (pCore 2 M).relIndex A := by
  have hi : A ⊓ extensionKernel h = A ⊓ pCore 2 M := by
    apply le_antisymm
    · exact le_inf inf_le_left (two_subgroup_le_core_of_le_extensionKernel h hz
        (A ⊓ extensionKernel h)
        (hA.of_injective (inclusion inf_le_left) (inclusion_injective _)) inf_le_right)
    · exact inf_le_inf_left A le_sup_right
  rw [←relIndex_ker,projection_kernel,←inf_relIndex_left A,hi,inf_relIndex_left]

/-- Coordinates at the opposite vertex, retaining its original graph embeddings
and actual order-eight point-core image. -/
structure OrbitPointCoordinates (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) where
  i : M →* FreeAmalgam T
  injective : Function.Injective i
  Z0 : Subgroup M
  Y : Subgroup M
  Z_le_Y : Z0 ≤ Y
  Y_le : Y ≤ T
  map_Z : Z0.map i = Z T (alpha T)
  map_Y : Y.map i = Q T (alpha T)
  map_Q : (pCore 2 M).map i = Q T o.c
  map_W : (W).map i = ⁅X T o.c,Ltilde T o.c⁆
  map_S : (omegaCenter T).map i = Z T o.b
  t : Equiv.Perm (Fin 6)
  swap : t.IsSwap
  g : Equiv.Perm (Fin 6)
  image_Z : Z0.map π = zpowers t
  image_Y : Y.map π =
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj g).toMonoidHom
  image_orbit : ((criticalOrbit T o.c o.b).comap i).map π = Y.map π

include h e hz hk in
/-- Construct the point coordinates on the reversed source critical pair.
The order calculation removes only the two-part of the cubic kernel. -/
theorem orbitPointCoordinates
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) :
    Nonempty (OrbitPointCoordinates h e hz hk o) := by
  obtain ⟨g,d,hga,hgd,hgb,hd,hdb,_⟩ := o.rebased
  let f := (MulAut.conj g⁻¹).toMonoidHom
  let i := f.comp (embedM T)
  have hi : Function.Injective i := (MulAut.conj g⁻¹).injective.comp (embedM_injective T)
  have hir : i.range = stabilizer T o.c := by
    rw [MonoidHom.range_comp]
    change (Mbar T).map f = _
    rw [←stabilizer_m_base,←stabilizer_act]
    change stabilizer T (act T g (alpha T)) = _
    rw [hga]
  have hQd : (Q T d).map f = Q T (alpha T) := by rw [←Q_act,hgd]
  have hZd : (Z T d).map f = Z T (alpha T) := by rw [←Z_act,hgd]
  have hiQ : (pCore 2 M).map i = Q T o.c := by
    rw [←map_map,←Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le,
      ←Q_act,hga]
  have hiW : (W).map i = ⁅X T o.c,Ltilde T o.c⁆ := by
    rw [←map_map,map_commutator,←graph_X h,←graph_component h,
      map_commutator,←X_act,←Ltilde_act,hga]
  have hiR : (T).map i = Q T o.b := by rw [←map_map,←Q_beta,←Q_act,hgb]
  have hiS : (omegaCenter T).map i = Z T o.b := by
    rw [←omegaCenter_map T i hi,hiR]
    simp only [Z,DistanceTwo.NaturalCore.edge_color o.adjacent_left,
      Bool.true_eq_false,if_false,edgeOmega]
  let Y := (Q T (alpha T)).comap i
  let Z0 := (Z T (alpha T)).comap i
  have hYG : Q T (alpha T) ≤ stabilizer T o.c :=
    DistanceTwo.NaturalCore.Q_le_endpoint_stabilizer o.adjacent_left o.adjacent_right
  have hYm : Y.map i = Q T (alpha T) := map_comap_eq_self (hir ▸ hYG)
  have hZQ : Z T (alpha T) ≤ Q T (alpha T) :=
    ((sourceGeometry h).omega_bound _ rfl (sourceDistance_pos h)).trans (omegaCenter_le _)
  have hZm : Z0.map i = Z T (alpha T) := map_comap_eq_self (hir ▸ hZQ.trans hYG)
  have hZY : Z0 ≤ Y := comap_mono hZQ
  have hYR : Y ≤ T := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [hYm,hiR]
    exact Q_le_adjacent_h T (DistanceTwo.NaturalCore.edge_color o.adjacent_left) o.adjacent_left
  have hYd : Y = (Q T d).comap (embedM T) := by
    dsimp only [Y,i]
    rw [←hQd,←comap_comap,comap_map_eq_self_of_injective (MulAut.conj g⁻¹).injective]
  have hZd0 : Z0 = (Z T d).comap (embedM T) := by
    dsimp only [Z0,i]
    rw [←hZd,←comap_comap,comap_map_eq_self_of_injective (MulAut.conj g⁻¹).injective]
  let A := criticalOrbit T o.c o.b
  let A0 := A.comap i
  have hAQ : A ≤ Q T (alpha T) := by
    rw [Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact map_mono o.orbit_le_core
  have hAm : A0.map i = A := map_comap_eq_self (hir ▸ hAQ.trans hYG)
  have hAY : A0 ≤ Y := comap_mono hAQ
  have hAp : IsPGroup 2 A0 := h.relative_radical.isPGroup.of_injective
    (inclusion (hAY.trans hYR)) (inclusion_injective _)
  have h8 : Nat.card (A0.map π) = 8 := by
    rw [permutation_image_card_of_two h e hz hk A0 hAp]
    have hh := relIndex_map_map_of_injective (pCore 2 M) A0 hi
    rw [hiQ,hAm] at hh
    rw [←hh]
    exact (preliminary_orbit_indices h e hz hk o).2.1
  have hZbQc : Z T o.b ≤ Q T o.c := by
    have hzbc : Z T o.b ≤ Z T o.c := by
      simp only [Z,critical_endpoint_color T (alpha T) rfl _ o.critical,
        DistanceTwo.NaturalCore.edge_color o.adjacent_left,Bool.true_eq_false,if_true,if_false]
      exact le_iSup_of_le o.b (le_iSup_of_le o.adjacent_right le_rfl)
    exact hzbc.trans (((sourceGeometry h).omega_bound o.c
      (critical_endpoint_color T (alpha T) rfl _ o.critical) (by
        rw [(sourceGeometry h).distance_constant o.c
          (critical_endpoint_color T (alpha T) rfl _ o.critical)]
        exact sourceDistance_pos h)).trans (omegaCenter_le _))
  have hcent : Y.map π ≤ centralizer (A0.map π : Set (Equiv.Perm (Fin 6))) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [projection_kernel]
    apply le_trans _ le_sup_right
    apply (map_le_map_iff_of_injective hi).mp
    rw [map_commutator,hYm,hAm,hiQ]
    exact (orbit_commutator_le_edge h e hz hk o.distance_two o.critical
      o.adjacent_left o.adjacent_right).trans hZbQc
  have heq := BeforePlane.eq_of_central_eight (A0.map π) (Y.map π)
    ((h.relative_radical.isPGroup.of_injective (inclusion hYR) (inclusion_injective _)).map π)
    (map_mono hAY) h8 hcent
  have helem : IsElementaryAbelian 2 (A0.map π) := by
    have hs (x : A0.map π) : x ^ 2 = 1 := by
      obtain ⟨a,ha,he⟩ := x.property
      have hpow := (orbit_square_central_edge h e hz hk o.distance_two o.critical
        o.adjacent_left o.adjacent_right ha).1
      have hcore : a ^ 2 ∈ pCore 2 M := by
        have hh := hZbQc hpow
        rw [←hiQ] at hh
        obtain ⟨z,hz,hez⟩ := hh
        have hez' : z = a ^ 2 := hi (by simpa only [map_pow] using hez)
        exact hez' ▸ hz
      have hker : a ^ 2 ∈ (π).ker := by rw [projection_kernel];exact mem_sup_right hcore
      apply Subtype.ext
      change x.val ^ 2 = 1
      rw [←he,←map_pow]
      exact hker
    exact {
      toIsMulCommutative := ⟨⟨fun a b =>
        Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_of_pow_eq_one (hs x)) a b⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  let := helem
  let : IsElementaryAbelian 2 (Y.map π) := heq.symm ▸ helem
  have hpoint : ∃ k, Y.map π =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj k).toMonoidHom := by
    rcases PlaneMovement.elementary_eight_models (Y.map π) (heq.symm ▸ h8) with hord | hpoint
    · obtain ⟨k,hk0⟩ := hord
      apply False.elim
      apply opposite_image_nonquadratic h e hz hk o.distance_two d hd
      have hh : graphImage h e hz hk (Q T d) = _ := hYd ▸ hk0
      rw [hh]
      exact PlaneMovement.quadratic_conjugate _ _ PlaneMovement.ordinary_core_quadratic k
    · exact hpoint
  obtain ⟨k,hk0⟩ := hpoint
  obtain ⟨t,ht,htZ⟩ := critical_image_eq_zpowers_transposition h e hz hk o.distance_two d hd
  have htZ0 : Z0.map π = zpowers t := by
    rw [hZd0]
    exact (critical_Z_image_eq h e hz hk o.distance_two d hd).trans htZ
  exact ⟨{
    i := i, injective := hi, Z0 := Z0, Y := Y, Z_le_Y := hZY, Y_le := hYR,
    map_Z := hZm, map_Y := hYm, map_Q := hiQ, map_W := hiW, map_S := hiS,
    t := t, swap := ht, g := k, image_Z := htZ0, image_Y := hk0, image_orbit := heq.symm }⟩

include h e hz hk in
/-- The coordinate embedding contains the entire critical orbit. -/
theorem OrbitPointCoordinates.orbit_map
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h))
    (s : OrbitPointCoordinates h e hz hk o) :
    ((criticalOrbit T o.c o.b).comap s.i).map s.i = criticalOrbit T o.c o.b := by
  apply map_comap_eq_self
  apply le_trans _ (s.map_Y ▸ map_le_range s.i s.Y)
  rw [Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
  exact map_mono o.orbit_le_core

include h e hz hk in
/-- The generating plane lies in the whole orbit commutator modulo the base layer. -/
theorem OrbitPointCoordinates.plane_moved
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h))
    (s : OrbitPointCoordinates h e hz hk o) :
    criticalPlane T o.c o.b ≤
      ⁅criticalOrbit T o.c o.b,stabilizer T (alpha T)⁆ ⊔ Z T (alpha T) := by
  let := h.relative_normal
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left (centralOmega L R) K)
  let q := π
  have hq := projection_surjective_of_distanceTwo h e hz hk o.distance_two
  let hkernel := moved_projection_kernel h e hz hk
  let ρ := NormalElementaryQuotient.representation W q hq hkernel
  have hmodel := moved_subgroup_cover_model h e hz hk o.distance_two
  let A0 := (criticalOrbit T o.c o.b).comap s.i
  have htY : s.t ∈ Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
      (MulAut.conj s.g).toMonoidHom :=
    s.image_Y ▸ map_mono s.Z_le_Y (s.image_Z ▸ mem_zpowers s.t)
  have hfix := BeforePlane.cover_fixed_le_pointCore_moved ρ hmodel s.g s.t htY s.swap
  have hZc : Z T o.c = (W ⊔ omegaCenter T).map s.i := by
    rw [Subgroup.map_sup,s.map_W,s.map_S]
    exact vertex_Z_eq_moved_sup_edge h e hz
      (critical_endpoint_color T (alpha T) rfl _ o.critical) o.adjacent_right
  intro z hzP
  have hzQ : z ∈ Q T (alpha T) := by
    rw [Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact map_mono o.orbit_le_core
      (criticalPlane_le_orbit (sourceGeometry h) o.distance_two o.critical o.b hzP)
  obtain ⟨z,hzCover,rfl⟩ := hZc.le (criticalPlane_le_opposite o.c o.b hzP)
  obtain ⟨w,hw,r,hr,rfl⟩ := mem_sup_of_normal_left.mp hzCover
  have hrC : r ∈ centralizer (s.Z0 : Set M) := by
    intro a ha
    exact (mem_omegaCenter_iff.mp hr).2.2 a ((s.Z_le_Y.trans s.Y_le) ha)
  have hzC : w*r ∈ centralizer (s.Z0 : Set M) := by
    intro a ha
    apply s.injective
    simp only [map_mul]
    simpa only [map_mul] using (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q T (alpha T) rfl)
      (s.map_Z ▸ mem_map_of_mem s.i ha) _ hzQ).symm
  have hwC : w ∈ centralizer (s.Z0 : Set M) := by
    simpa only [mul_inv_cancel_right] using
      (centralizer (s.Z0 : Set M)).mul_mem hzC
        ((centralizer (s.Z0 : Set M)).inv_mem hrC)
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
  rw [←s.image_Y,←s.image_orbit,←NormalElementaryQuotient.commutatorSpace_eq W q hq hkernel] at hwm
  have hwcomm : w ∈ ⁅W,A0⁆ := hwm
  have hwmap : s.i w ∈ ⁅criticalOrbit T o.c o.b,stabilizer T (alpha T)⁆ := by
    have hh := mem_map_of_mem s.i hwcomm
    rw [map_commutator,OrbitPointCoordinates.orbit_map h e hz hk o s,commutator_comm] at hh
    apply commutator_mono le_rfl _ hh
    rw [s.map_W]
    exact (le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer o.c).trans (X_normalized T o.c))).trans
      (critical_X_le_vertex h e o.c
        (critical_endpoint_color T (alpha T) rfl _ o.critical) (alpha T)
        (critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
          (alpha T) rfl (sourceDistance_pos h) o.c
          (critical_endpoint_color T (alpha T) rfl _ o.critical) o.critical))
  have hrZ : s.i r ∈ Z T (alpha T) := by
    have hrb : s.i r ∈ Z T o.b := s.map_S ▸ mem_map_of_mem s.i hr
    have hZb : Z T o.b ≤ Z T (alpha T) := by
      simp only [Z,show color T (alpha T) = false from rfl,
        DistanceTwo.NaturalCore.edge_color o.adjacent_left,Bool.true_eq_false,if_true,if_false]
      exact le_iSup_of_le o.b (le_iSup_of_le o.adjacent_left le_rfl)
    exact hZb hrb
  rw [map_mul]
  exact mul_mem_sup hwmap hrZ


include h e hz hk in
/-- The source orbit does not centralize its generating plane. -/
theorem OrbitPointCoordinates.plane_movement
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h))
    (s : OrbitPointCoordinates h e hz hk o) :
    ⁅criticalOrbit T o.c o.b,criticalPlane T o.c o.b⁆ ≠ ⊥ := by
  intro hzero
  have hp := h.relative_radical.isPGroup
  have hQR := h.relative_radical.twoCore_le
  let A := criticalOrbit T o.c o.b
  let A0 := A.comap s.i
  let q := π
  have hAY : A0 ≤ s.Y := by
    apply (map_le_map_iff_of_injective s.injective).mp
    rw [OrbitPointCoordinates.orbit_map h e hz hk o s,s.map_Y,Q_alpha T hp hQR]
    exact map_mono o.orbit_le_core
  have hYp : IsPGroup 2 s.Y := hp.of_injective (inclusion s.Y_le) (inclusion_injective _)
  have hIE : s.Y ⊓ extensionKernel h ≤ pCore 2 M :=
    two_subgroup_le_core_of_le_extensionKernel h hz (s.Y ⊓ extensionKernel h)
      (hYp.of_injective (inclusion inf_le_left) (inclusion_injective _)) inf_le_right
  have hYs : s.Y ≤ A0 ⊔ pCore 2 M := by
    intro y hy
    obtain ⟨a,ha,he⟩ := s.image_orbit.ge (mem_map_of_mem q hy)
    have hE : a⁻¹*y ∈ extensionKernel h := by
      rw [←projection_kernel h e hz hk]
      change q (a⁻¹*y) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hQ : a⁻¹*y ∈ pCore 2 M := hIE ⟨s.Y.mul_mem (s.Y.inv_mem (hAY ha)) hy,hE⟩
    have hh := mul_mem_sup ha hQ
    simpa only [mul_inv_cancel_left] using hh
  have hQa : Q T (alpha T) ≤ A ⊔ Q T o.c := by
    have hh := map_mono (f := s.i) hYs
    rw [s.map_Y,Subgroup.map_sup,OrbitPointCoordinates.orbit_map h e hz hk o s,s.map_Q] at hh
    exact hh
  have hAQ : A ≤ Q T (alpha T) := by
    rw [Q_alpha T hp hQR]
    exact map_mono o.orbit_le_core
  have hc0 := critical_endpoint_color T (alpha T) rfl _ o.critical
  have hZcG : Z T o.c ≤ stabilizer T (alpha T) :=
    critical_Z_le_stabilizer T (sourceGeometry h) (alpha T) rfl
      (sourceDistance_pos h) o.critical
  have hDplane : ⁅A,Z T o.c⁆ ≤ criticalPlane T o.c o.b := by
    apply le_criticalPlane_of_commutator_le _
      (le_normalizer_iff_commutator_le_right.mp
        ((hAQ.trans (DistanceTwo.NaturalCore.Q_le_endpoint_stabilizer o.adjacent_left o.adjacent_right)).trans
          (Z_normalized T o.c)))
    exact (commutator_mono le_rfl
      (le_normalizer_iff_commutator_le_left.mp (hZcG.trans (criticalOrbit_normalized o.c o.b)))).trans
      (orbit_commutator_le_edge h e hz hk o.distance_two
        o.critical o.adjacent_left o.adjacent_right)
  have hQcent : Q T o.c ≤ centralizer (Z T o.c : Set (FreeAmalgam T)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q T o.c hc0))
  have hinter : ⁅Q T (alpha T),Z T o.c⁆ ≤
      criticalPlane T o.c o.b := by
    apply commutator_le.mpr
    intro x hx z hz
    obtain ⟨y,hyY,rfl⟩ := s.map_Y.ge hx
    obtain ⟨a,ha,k,hk,rfl⟩ := mem_sup_of_normal_right.mp (hYs hyY)
    have hkc : Commute (s.i k) z := (hQcent (s.map_Q ▸ mem_map_of_mem s.i hk) z hz).symm
    rw [map_mul,commutatorElement_mul_left_eq_conj_mul,hkc.commutator_eq]
    simp only [mul_one,mul_inv_cancel,one_mul]
    exact hDplane (commutator_mem_commutator ha hz)
  have hcent : Q T (alpha T) ≤
      centralizer (criticalPlane T o.c o.b : Set (FreeAmalgam T)) := by
    apply hQa.trans
    apply sup_le (commutator_eq_bot_iff_le_centralizer.mp hzero)
    exact hQcent.trans (centralizer_le (criticalPlane_le_opposite o.c o.b))
  have hX : ⁅Q T (alpha T),Z T o.c⁆ ≤ X T (alpha T) := by
    intro x hx
    apply mem_omegaCenter_iff.mpr
    exact ⟨DistanceTwo.NaturalCore.local_commutator_le_Q (sourceGeometry h) o.distance_two o.critical hx,
      DistanceTwo.NaturalCore.local_commutator_pow_two (sourceGeometry h) o.distance_two o.critical
        o.adjacent_left o.adjacent_right hx,
      le_centralizer_iff.mp hcent (hinter hx)⟩
  exact cubic_not_coreExhaustion h hz hk
    (coreExhaustion_of_critical_commutator_le h e hz _ o.critical (hX.trans le_sup_right))


include h e hz hk in
/-- The whole orbit is moved by the original component modulo the base layer. -/
theorem preliminary_full_movement
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) :
    criticalOrbitNative T o.c o.b =
      ⁅pResidual 2 M,criticalOrbitNative T o.c o.b⁆ ⊔ orbitLayer T := by
  obtain ⟨s⟩ := orbitPointCoordinates h e hz hk o
  have hgen : pResidual 2 M ⊔ T = ⊤ := by
    rw [h.relative_residual]
    apply top_unique
    intro x _
    obtain ⟨k,hkK,r,hr,rfl⟩ := h.relative_product x
    exact mul_mem_sup hkK hr
  exact full_movement_of_plane (sourceGeometry h) (pResidual 2 M)
    h.relative_radical.isPGroup hgen o.distance_two o.critical
    o.adjacent_left o.adjacent_right o.orbit_le_core (OrbitPointCoordinates.plane_moved h e hz hk o s)

include h e hz hk in
/-- The literal fixed preimage is central in the orbit, by three subgroups
and full movement; no choice of a natural subgroup is involved. -/
theorem preliminary_fixedKernel_central
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) :
    orbitFixedKernel (pResidual 2 M) T o.c o.b ≤
      centralizer (criticalOrbitNative T o.c o.b : Set M) := by
  apply fixedKernel_central_of_full_movement (pResidual 2 M)
    h.relative_radical.isPGroup h.relative_radical.twoCore_le o.orbit_le_core
  · rw [h.relative_residual]
    exact orbit_commutator_centralizes_component h e hz hk o.distance_two
      o.critical o.adjacent_left o.adjacent_right
  · exact preliminary_full_movement h e hz hk o

include h e hz hk in
/-- The source plane is moved by its whole orbit on the original pair. -/
theorem preliminary_plane_movement
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) :
    ⁅criticalOrbit T o.c o.b,criticalPlane T o.c o.b⁆ ≠ ⊥ := by
  obtain ⟨s⟩ := orbitPointCoordinates h e hz hk o
  exact OrbitPointCoordinates.plane_movement h e hz hk o s

include h e hz hk in
/-- Quotient recognition is the only remaining distance-two orbit premise.
Full movement, the fixed-kernel centrality and the contradictory plane
movement are supplied by the actual cubic source geometry. -/
theorem false_of_preliminary_recognized
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) (hr : o.Recognized) : False :=
  o.false_of_recognized h.relative_radical.isPGroup h.relative_radical.twoCore_le
    (paired_commutator_elementary h e hz hk o.distance_two o.critical
      o.adjacent_left o.adjacent_right o.rebased)
    (preliminary_fixedKernel_central h e hz hk o)
    (preliminary_plane_movement h e hz hk o) hr

include h e hz hk in
/-- Literal whole-core exhaustion from the sole remaining recognition step;
the earlier independent plane-intersection premise is unnecessary. -/
theorem coreExhaustion_of_selected_recognition
    (hb : sourceDistance h = 2)
    (hr : (selectedOrbitPair h e hz hk hb).Recognized) : CoreExhaustion L R :=
  (false_of_preliminary_recognized h e hz hk _ hr).elim

end AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
