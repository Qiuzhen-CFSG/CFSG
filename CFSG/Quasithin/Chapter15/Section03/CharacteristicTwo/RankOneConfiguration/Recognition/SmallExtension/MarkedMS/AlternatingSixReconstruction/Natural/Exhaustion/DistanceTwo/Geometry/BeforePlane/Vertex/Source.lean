module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane.Exponent.Source
/-!
# Preliminary critical orbits before full edge-image identification

The favorable pair retains its literal orbit and common edge. Normal closure
and the source commutator identities control its squares and the opposite
vertex-core image without identifying that image with the whole radical.
Both central covers of orders sixteen and thirty-two are retained.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871.
Final distance-two exhaustion still requires the critical-plane calculations.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane

theorem eq_of_central_eight (A T : Subgroup (Equiv.Perm (Fin 6)))
    (hp : IsPGroup 2 T) (hA : A ≤ T) (h8 : Nat.card A = 8)
    (hc : T ≤ centralizer (A : Set (Equiv.Perm (Fin 6)))) : T = A := by
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  have hPc : Nat.card (P : Subgroup (Equiv.Perm (Fin 6))) = 16 := by
    rw [P.card_eq_multiplicity,Nat.card_perm,Nat.card_fin]
    decide +kernel
  have hT16 : Nat.card T ≤ 16 := (card_le_of_le hP).trans_eq hPc
  have hAc : Nat.card (A.subgroupOf T) = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv).trans h8
  have hAZ : A.subgroupOf T ≤ center T := by
    intro a ha
    rw [mem_center_iff]
    intro t
    apply Subtype.ext
    exact (hc t.property a ha).symm
  have hZ8 : 8 ≤ Nat.card (center T) := hAc ▸ card_le_of_le hAZ
  have hmul := (center T).card_mul_index
  have hi : (center T).index ≤ 2 := by nlinarith
  have hpos := Nat.pos_of_ne_zero (index_ne_zero_of_finite (H := center T))
  let : IsCyclic (T ⧸ center T) := isCyclic_of_card_dvd_prime (p := 2) (by
    change (center T).index ∣ 2
    have hh : (center T).index = 1 ∨ (center T).index = 2 := by omega
    rcases hh with hh | hh <;> simp [hh])
  let := isMulCommutative_of_isCyclic_quotient_center_self T
  have hne : Nat.card T ≠ 16 := by
    intro he
    have heq : T = P := eq_of_le_of_card_ge hP (by omega)
    let : IsMulCommutative (P : Subgroup (Equiv.Perm (Fin 6))) := heq ▸ inferInstance
    exact alternatingGroup.SixSubgroupObstructions.not_injective_of_sylow_involutions_commute P
      (fun a b _ _ => mul_comm a b)
      (alternatingGroup (Fin 6)).subtype Subtype.coe_injective
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hn4 : n < 4 := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    change 2 ^ n < 16
    omega
  have hT8 : Nat.card T ≤ 8 := by
    rw [hn]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n ≤ 3)
  exact (eq_of_le_of_card_ge hA (hT8.trans_eq h8.symm)).symm

variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} {geo : Geometry R}
  {o : PreliminaryPair R geo} (s : ImageModel o)

include s in
theorem opposite_core_image
    (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R) :
    ((Q R o.c).comap (embedM R)).map s.projection =
      (o.opposite.comap (embedM R)).map s.projection := by
  let A := (o.opposite.comap (embedM R)).map s.projection
  let T := ((Q R o.c).comap (embedM R)).map s.projection
  have hT : IsPGroup 2 T :=
    ((Q_isPGroup R hp hQR o.c (critical_endpoint_color R (alpha R) rfl _ o.critical)).comap_of_injective
      (embedM R) (embedM_injective R)).map s.projection
  have hA : A ≤ T := map_mono (comap_mono o.opposite_le)
  have hm : s.actor.map s.projection.range.subtype = A := by
    rw [ImageModel.actor,map_map]
    rfl
  let := o.quotient_elementary
  have h8 : Nat.card A = 8 := by
    rw [←hm,card_map_of_injective Subtype.coe_injective,s.actor_card hp hQR]
    exact (s.strict_indices hp hQR).1
  apply eq_of_central_eight A T hT hA h8
  rintro _ ⟨q,hq,rfl⟩ _ ⟨a,ha,rfl⟩
  have hcomm : ⁅q,a⁆ ∈ pCore 2 M := by
    have hh := o.opposite_commutator
      (commutator_mem_commutator hq ha)
    have hZb : Z R o.b ≤ Z R (alpha R) := by
      simp only [Z,show color R (alpha R) = false from rfl,
        DistanceTwo.NaturalCore.edge_color o.adjacent_left,Bool.true_eq_false,if_true,if_false]
      exact le_iSup_of_le o.b (le_iSup_of_le o.adjacent_left le_rfl)
    have hZQ := (geo.omega_bound (alpha R) rfl (by
      change 0 < geo.b R
      rw [o.distance_two]
      decide)).trans (omegaCenter_le _)
    have hhQ := hZQ (hZb hh)
    rw [Q_alpha R hp hQR] at hhQ
    obtain ⟨x,hx,he⟩ := hhQ
    have he' : x = ⁅q,a⁆ := (embedM_injective R) (by simpa only [map_commutatorElement] using he)
    exact he' ▸ hx
  have he : s.projection ⁅q,a⁆ = 1 := by
    have hh : ⁅q,a⁆ ∈ s.projection.ker := s.kernel.symm ▸ hcomm
    exact hh
  rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm] at he
  exact he.symm

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane
open LocalImages LargeDistance PlaneMovement
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)

include h e hz in
private theorem vertex_edge_coordinates {c b : Vertex d.radical}
    (hc : color d.radical c = false) (hcb : Adjacent d.radical c b) :
    ∃ i : d.overgroup →* FreeAmalgam d.radical, Function.Injective i ∧
      i.range = stabilizer d.radical c ∧ d.radical.map i = Q d.radical b ∧
      (pCore 2 d.overgroup).map i = Q d.radical c ∧
      (replacementMoved d).map i = U d.radical c ∧
      (pResidual 2 d.overgroup).map i = Ltilde d.radical c := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common d.radical c b).mp hcb
  · rcases hg with ⟨rfl,rfl⟩
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
    refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_,?_,?_,?_⟩
    · have he := stabilizer_act d.radical g (alpha d.radical)
      dsimp only [i]
      rw [MonoidHom.range_comp]
      change (Mbar d.radical).map (MulAut.conj g⁻¹).toMonoidHom = _
      simpa only [alpha,act_mVertex,one_mul,stabilizer_m_base] using he.symm
    · have he := Q_act d.radical g (beta d.radical)
      rw [Q_beta] at he
      simpa only [beta,act_hVertex,one_mul,Q_beta,map_map] using he.symm
    · have he := Q_act d.radical g (alpha d.radical)
      rw [Q_alpha d.radical (replacement_radical_isPGroup h d)
        (replacement_core_le_radical h d)] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · have he := U_act d.radical g (alpha d.radical)
      rw [(CentralLayer.replacement_centralLayer d e hz h).U_eq_moved] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · have he := Ltilde_act d.radical g (alpha d.radical)
      rw [Ltilde_alpha] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
  · rw [hg.1] at hc
    cases hc


include h e hz hn in
theorem critical_core_image_pointCore
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    (o : PreliminaryPair d.radical (replacementGeometry h d))
    (Y : Subgroup d.overgroup) (hYR : Y ≤ d.radical)
    (i : d.overgroup →* FreeAmalgam d.radical) (hi : Function.Injective i)
    (hiY : Y.map i = Q d.radical (alpha d.radical))
    (hiQ : (pCore 2 d.overgroup).map i = Q d.radical o.c)
    (hiW : (replacementMoved d).map i = U d.radical o.c)
    (hiS : (omegaCenter d.radical).map i = Z d.radical o.b) :
    ∃ g, Y.map (Recognition.sourceProjection h e hz hn d) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj g).toMonoidHom := by
  let q := Recognition.sourceProjection h e hz hn d
  let s : ImageModel o := {
    projection := q
    kernel := Recognition.sourceProjection_kernel h e hz hn d
    component_image := Recognition.sourceProjection_component h e hz hn d }
  have hp := replacement_radical_isPGroup h d
  have hQR := replacement_core_le_radical h d
  let := o.quotient_elementary
  let A := criticalOrbit d.radical o.c o.b
  let A0 := A.comap i
  have hAQ : A ≤ Q d.radical (alpha d.radical) := by
    rw [Q_alpha d.radical hp hQR]
    exact map_mono o.orbit_le_core
  have hAm : A0.map i = A := map_comap_eq_self
    (hAQ.trans (hiY ▸ map_le_range i Y))
  have hAY : A0 ≤ Y := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [hAm,hiY]
    exact hAQ
  have h8 : Nat.card (A0.map q) = 8 := by
    rw [←relIndex_ker,Recognition.sourceProjection_kernel]
    have hh := relIndex_map_map_of_injective (pCore 2 d.overgroup) A0 hi
    rw [hiQ,hAm] at hh
    rw [←hh]
    exact (s.strict_indices hp hQR).2.1
  have hZbQc : Z d.radical o.b ≤ Q d.radical o.c := by
    have hZbZc : Z d.radical o.b ≤ Z d.radical o.c := by
      simp only [Z,critical_endpoint_color d.radical (alpha d.radical) rfl _ o.critical,
        DistanceTwo.NaturalCore.edge_color o.adjacent_left,Bool.true_eq_false,if_true,if_false]
      exact le_iSup_of_le o.b (le_iSup_of_le o.adjacent_right le_rfl)
    exact hZbZc.trans (((replacementGeometry h d).omega_bound o.c
      (critical_endpoint_color d.radical (alpha d.radical) rfl _ o.critical)
      (by
        rw [(replacementGeometry h d).distance_constant o.c
          (critical_endpoint_color d.radical (alpha d.radical) rfl _ o.critical)]
        change 0 < replacementDistance h d
        omega)).trans (omegaCenter_le _))
  have hcent : Y.map q ≤ centralizer (A0.map q : Set (Equiv.Perm (Fin 6))) := by
    have hcomm : ⁅Y,A0⁆ ≤ pCore 2 d.overgroup := by
      apply (map_le_map_iff_of_injective hi).mp
      rw [map_commutator,hiY,hAm,hiQ]
      exact (orbit_commutator_le_edge_of_transposition h e hz hn d hb hlarge
        o.critical o.adjacent_left o.adjacent_right).trans
        hZbQc
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [Recognition.sourceProjection_kernel]
    exact hcomm
  have heq := eq_of_central_eight (A0.map q) (Y.map q)
    ((hp.of_injective (inclusion hYR) (inclusion_injective _)).map q)
    (map_mono hAY) h8 hcent
  have helem : IsElementaryAbelian 2 (A0.map q) := by
    have hs (x : A0.map q) : x ^ 2 = 1 := by
      obtain ⟨a,ha,he⟩ := x.property
      have hpow := (Exponent.orbit_square_central_edge h e hz hn d hb hlarge
        o.critical o.adjacent_left o.adjacent_right ha).1
      have hker : a ^ 2 ∈ q.ker := by
        rw [Recognition.sourceProjection_kernel]
        have hh := hZbQc hpow
        rw [←hiQ] at hh
        obtain ⟨z,hz,hez⟩ := hh
        have hez' : z = a ^ 2 := hi (by simpa only [map_pow] using hez)
        exact hez' ▸ hz
      apply Subtype.ext
      change x.val ^ 2 = 1
      rw [←he,←map_pow]
      exact hker
    exact {
      toIsMulCommutative := ⟨⟨fun a b =>
        Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_of_pow_eq_one (hs x)) a b⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  let := helem
  let : IsElementaryAbelian 2 (Y.map q) := heq.symm ▸ helem
  rcases elementary_eight_models (Y.map q) (heq.symm ▸ h8) with hord | hpoint
  · obtain ⟨g,hg⟩ := hord
    apply False.elim
    apply critical_image_nonquadratic h e hz hn d hb hlarge o.critical
      o.adjacent_left o.adjacent_right Y i hi hiY hiW hiS
    rw [hg]
    exact quadratic_conjugate _ _ ordinary_core_quadratic g
  · exact hpoint

include h e hz hn in
/-- The actual favorable pair has point-core vertex coordinates, even when
its whole radical has the larger Sylow image. -/
theorem exists_preliminary_pointCore_coordinates
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) :
    ∃ o : PreliminaryPair d.radical (replacementGeometry h d),
      o.b = beta d.radical ∧
      ∃ (Y : Subgroup d.overgroup) (i : d.overgroup →* FreeAmalgam d.radical)
        (g : Equiv.Perm (Fin 6)),
        Function.Injective i ∧ Y ≤ d.radical ∧
        Y.map i = Q d.radical (alpha d.radical) ∧
        (pCore 2 d.overgroup).map i = Q d.radical o.c ∧
        (replacementMoved d).map i = U d.radical o.c ∧
        (omegaCenter d.radical).map i = Z d.radical o.b ∧
        d.radical.map i = Q d.radical o.b ∧
        Y.map (Recognition.sourceProjection h e hz hn d) =
          Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨o,hbase⟩ := exists_preliminaryPair_base (replacementGeometry h d)
    (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)
    (source_localData h e hz hn d hb hlarge) hb
  have hc0 := critical_endpoint_color d.radical (alpha d.radical) rfl _ o.critical
  obtain ⟨i,hi,hir,hiR,hiQ,hiW,hiL⟩ :=
    vertex_edge_coordinates h e hz d hc0 o.adjacent_right
  let Y := (Q d.radical (alpha d.radical)).comap i
  have hYm : Y.map i = Q d.radical (alpha d.radical) := by
    rw [map_comap_eq,hir,inf_eq_right.mpr
      (DistanceTwo.NaturalCore.Q_le_endpoint_stabilizer o.adjacent_left o.adjacent_right)]
  have hYR : Y ≤ d.radical := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [hYm,hiR]
    exact Q_le_adjacent_h d.radical (DistanceTwo.NaturalCore.edge_color o.adjacent_left)
      o.adjacent_left
  have hiS : (omegaCenter d.radical).map i = Z d.radical o.b := by
    rw [←omegaCenter_map d.radical i hi,hiR]
    simp only [Z,DistanceTwo.NaturalCore.edge_color o.adjacent_left,Bool.true_eq_false,if_false,edgeOmega]
  obtain ⟨g,hg⟩ := critical_core_image_pointCore h e hz hn d hb hlarge o Y hYR i hi hYm hiQ hiW hiS
  exact ⟨o,hbase,Y,i,g,hi,hYR,hYm,hiQ,hiW,hiS,hiR,hg⟩

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
