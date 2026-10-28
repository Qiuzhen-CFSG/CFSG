module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.CentralLayer.Edges
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates.Images
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Structure.PlaneContainment

/-!
# Plane generation for the whole central moved cover

The literal edge coordinates transport the entire replacement moved layer,
not a natural complement. Reversing a critical pair transports its order-two
image. Thus an upper bound of eight on the native edge index bounds the
critical-plane index by four. A lower bound of four on the native displacement
then forces that displacement and the edge seed to generate the whole plane.

The last theorem applies this calculation to the actual ordered orbit selected
by the favorable-pair argument. The two native numerical bounds and the
opposite-layer intersection bound remain explicit source obligations; the
distance-two assembly owner must prove them. No splitting of the central
attachment is used. Adapted from Chapter C's CriticalPlane/Cardinality and
CriticalPlane/FullMovement; source: MS93 (3.3), (3.6), printed pp.867 and 871.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (d : Replacement L R)

include h e hz in
/-- The three native layers have their exact incident-edge coordinates,
including the whole central cover. -/
theorem edge_coordinates {c b : Vertex d.radical}
    (hc : color d.radical c = false) (hcb : Adjacent d.radical c b) :
    ∃ i : d.overgroup →* FreeAmalgam d.radical, Function.Injective i ∧
      d.radical.map i = Q d.radical b ∧
      (replacementMoved d).map i = U d.radical c ∧
      (omegaCenter d.radical).map i = Z d.radical b := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common d.radical c b).mp hcb
  · rcases hg with ⟨rfl,rfl⟩
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
    have hi : Function.Injective i :=
      (MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical)
    have hiR : d.radical.map i = Q d.radical (hVertex d.radical g) := by
      have he := Q_act d.radical g (beta d.radical)
      rw [Q_beta] at he
      simpa only [beta,act_hVertex,one_mul,Q_beta,map_map] using he.symm
    refine ⟨i,hi,hiR,?_,?_⟩
    · have he := U_act d.radical g (alpha d.radical)
      rw [(CentralLayer.replacement_centralLayer d e hz h).U_eq_moved] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · rw [←omegaCenter_map d.radical i hi,hiR]
      simp only [Z,show color d.radical (hVertex d.radical g) = true from rfl,
        Bool.true_eq_false,if_false,edgeOmega]
  · rw [hg.1] at hc
    cases hc

include h e hz in
/-- The native whole-cover index is exactly the literal edge-layer index. -/
theorem edge_layer_relIndex {c b : Vertex d.radical}
    (hc : color d.radical c = false) (hcb : Adjacent d.radical c b) :
    (Z d.radical b).relIndex (Z d.radical c) =
      (omegaCenter d.radical).relIndex (replacementMoved d ⊔ omegaCenter d.radical) := by
  obtain ⟨i,hi,hiR,hiW,hiS⟩ := edge_coordinates h e hz d hc hcb
  rw [CentralLayer.Z_eq_moving_sup_edge_at h e hz d hc hcb,←hiW,←hiS,
    ←Subgroup.map_sup,relIndex_map_map_of_injective _ _ hi]

include h e hz in
/-- The displacement index also transports without quotienting out the
central attachment. -/
theorem edge_displacement_relIndex {c b : Vertex d.radical}
    (hc : color d.radical c = false) (hcb : Adjacent d.radical c b) :
    (Z d.radical b).relIndex (⁅Q d.radical b,U d.radical c⁆ ⊔ Z d.radical b) =
      (omegaCenter d.radical).relIndex
        (⁅d.radical,replacementMoved d⁆ ⊔ omegaCenter d.radical) := by
  obtain ⟨i,hi,hiR,hiW,hiS⟩ := edge_coordinates h e hz d hc hcb
  rw [←hiR,←hiW,←hiS,←map_commutator,←Subgroup.map_sup,
    relIndex_map_map_of_injective _ _ hi]

include h e hz in
/-- Fullness in the actual edge quotient identifies the orbit displacement
with that of the entire opposite moved cover. -/
theorem orbit_displacement {c b : Vertex d.radical}
    (hc : color d.radical c = false) (hcb : Adjacent d.radical c b)
    (himage : criticalOrbit d.radical c b ⊔ Q d.radical c = Q d.radical b) :
    ⁅criticalOrbit d.radical c b,Z d.radical c⁆ =
      ⁅Q d.radical b,U d.radical c⁆ := by
  have hAG : criticalOrbit d.radical c b ≤ stabilizer d.radical c :=
    (show criticalOrbit d.radical c b ≤ Q d.radical b from
      le_sup_left.trans_eq himage).trans
        (fun _ hx => hx.2 c (adjacent_symm d.radical hcb))
  have hC : Q d.radical c ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical c hc))
  calc
    ⁅criticalOrbit d.radical c b,Z d.radical c⁆ =
        ⁅Z d.radical c,criticalOrbit d.radical c b⁆ := commutator_comm _ _
    _ = ⁅Z d.radical c,Q d.radical b⁆ :=
      commutator_eq_of_centralizing_sup ((sup_comm _ _).trans himage) hC
        (hAG.trans (Z_normalized d.radical c))
    _ = ⁅Q d.radical b,Z d.radical c⁆ := commutator_comm _ _
    _ = ⁅Q d.radical b,U d.radical c⁆ :=
      CentralLayer.edge_displacement_eq_moving h e hz d hc hcb

/-- Reversing and rebasing a critical pair preserves the literal order-two
image; no model action or chosen complement is involved. -/
theorem critical_reverse_image_order_two
    (hl : LocalCalculations d.radical (replacementGeometry h d))
    (hb : replacementDistance h d = 2) {c : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl)) :
    (Q d.radical (alpha d.radical)).relIndex (Z d.radical c) = 2 := by
  have hc0 := critical_endpoint_color d.radical (alpha d.radical) rfl _ hc
  have hrev := critical_reverse d.radical (replacementGeometry h d) hl.edge_centralizer
    (alpha d.radical) rfl (by change 0 < replacementDistance h d; omega) c hc0 hc
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical hc0
  have hcol : color d.radical (act d.radical g⁻¹ (mVertex d.radical g)) = false := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  have hnew := (criticalPair_act_iff d.radical g⁻¹ (mVertex d.radical g) (alpha d.radical)
    ((replacementGeometry h d).exists_critical (mVertex d.radical g) hc0)
    ((replacementGeometry h d).exists_critical
      (act d.radical g⁻¹ (mVertex d.radical g)) hcol)).mpr hrev
  have hcrit : CriticalPair d.radical (alpha d.radical) (mVertex d.radical g⁻¹)
      ((replacementGeometry h d).exists_critical _ rfl) := by
    simpa only [alpha,act_mVertex,mul_inv_cancel,one_mul] using hnew
  have htwo := hl.image_two _ hcrit
  have he := relIndex_map_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
    (Q d.radical (mVertex d.radical g⁻¹)) (Z d.radical (alpha d.radical))
      (MulAut.conj g⁻¹).injective
  rw [←Q_act,←Z_act] at he
  simpa only [alpha,act_mVertex,inv_mul_cancel,one_mul] using he.trans htwo

variable (hl : LocalCalculations d.radical (replacementGeometry h d))
  (hb : replacementDistance h d = 2)
  (hlarge : ¬ core d.radical (alpha d.radical) ≤
    (frattini (Q d.radical (alpha d.radical))).map
      (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))

include e hz hl hb in
/-- An edge-index upper bound, together with the maximal-intersection
identity, gives the exact upper bound needed by the plane-generation argument. -/
theorem plane_edge_relIndex_le_four
    (h8 : (omegaCenter d.radical).relIndex
      (replacementMoved d ⊔ omegaCenter d.radical) ≤ 8)
    {c b : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl))
    (hab : Adjacent d.radical (alpha d.radical) b) (hcb : Adjacent d.radical c b)
    (hplane : criticalPlane d.radical c b =
      Z d.radical c ⊓ Q d.radical (alpha d.radical)) :
    (Z d.radical b).relIndex (criticalPlane d.radical c b) ≤ 4 := by
  have hc0 := critical_endpoint_color d.radical (alpha d.radical) rfl _ hc
  have hrev := critical_reverse_image_order_two h d hl hb hc
  have hedge := edge_layer_relIndex h e hz d hc0 hcb
  have hmid : (criticalPlane d.radical c b).relIndex (Z d.radical c) = 2 := by
    rw [hplane,inf_relIndex_left]
    exact hrev
  have hmul := relIndex_mul_relIndex (Z d.radical b) (criticalPlane d.radical c b)
    (Z d.radical c) (edge_Z_le_criticalPlane (replacementGeometry h d) hc hab hcb)
    (criticalPlane_le_opposite c b)
  rw [hmid,hedge] at hmul
  omega

include e hz hl hb in
/-- The two native bounds force the actual orbit displacement and the edge
seed to generate the entire maximal critical plane. -/
theorem displacement_sup_edge_eq_plane
    (h8 : (omegaCenter d.radical).relIndex
      (replacementMoved d ⊔ omegaCenter d.radical) ≤ 8)
    (h4 : 4 ≤ (omegaCenter d.radical).relIndex
      (⁅d.radical,replacementMoved d⁆ ⊔ omegaCenter d.radical))
    {c b : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl))
    (hab : Adjacent d.radical (alpha d.radical) b) (hcb : Adjacent d.radical c b)
    (hplane : criticalPlane d.radical c b =
      Z d.radical c ⊓ Q d.radical (alpha d.radical))
    (himage : criticalOrbit d.radical c b ⊔ Q d.radical c = Q d.radical b) :
    ⁅criticalOrbit d.radical c b,Z d.radical c⁆ ⊔ Z d.radical b =
      criticalPlane d.radical c b := by
  let A := criticalOrbit d.radical c b
  let D := ⁅A,Z d.radical c⁆ ⊔ Z d.radical b
  have hc0 := critical_endpoint_color d.radical (alpha d.radical) rfl _ hc
  have hAQ : A ≤ Q d.radical (alpha d.radical) := by
    dsimp only [A]
    rw [criticalOrbit,Q_alpha d.radical
      (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
    exact map_mono (hl.orbit_core c b hc hab hcb)
  have hAR : A ≤ Q d.radical b := le_sup_left.trans_eq himage
  have hAnZ : A ≤ normalizer (Z d.radical c : Set (FreeAmalgam d.radical)) :=
    (hAR.trans (fun _ hx => hx.2 c (adjacent_symm d.radical hcb))).trans
      (Z_normalized d.radical c)
  have hZAn : Z d.radical c ≤ normalizer (A : Set (FreeAmalgam d.radical)) :=
    (critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical) rfl
      (by change 0 < replacementDistance h d; omega) hc).trans
      (criticalOrbit_normalized c b)
  have hDY : D ≤ criticalPlane d.radical c b := by
    apply sup_le _ (edge_Z_le_criticalPlane (replacementGeometry h d) hc hab hcb)
    rw [hplane]
    exact le_inf (le_normalizer_iff_commutator_le_right.mp hAnZ)
      ((le_normalizer_iff_commutator_le_left.mp hZAn).trans hAQ)
  have hZD : Z d.radical b ≤ D := le_sup_right
  have hfour : 4 ≤ (Z d.radical b).relIndex D := by
    dsimp only [D]
    rw [orbit_displacement h e hz d hc0 hcb himage,
      edge_displacement_relIndex h e hz d hc0 hcb]
    exact h4
  have hbound := plane_edge_relIndex_le_four h e hz d hl hb h8 hc hab hcb hplane
  have hmul := relIndex_mul_relIndex (Z d.radical b) D
    (criticalPlane d.radical c b) hZD hDY
  let := finite_Z d.radical c
  let : Finite (criticalPlane d.radical c b) :=
    Finite.of_injective (inclusion (criticalPlane_le_opposite c b)) (inclusion_injective _)
  have hpos : 0 < D.relIndex (criticalPlane d.radical c b) :=
    Nat.pos_of_ne_zero (index_ne_zero_of_finite
      (H := D.subgroupOf (criticalPlane d.radical c b)))
  have hone : D.relIndex (criticalPlane d.radical c b) = 1 := by nlinarith
  exact le_antisymm hDY (relIndex_eq_one.mp hone)

include hb in
/-- The preceding equality supplies the literal plane-movement premise used
by the paired-orbit assembly. -/
theorem plane_movement
    {c b : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl))
    (heq : ⁅criticalOrbit d.radical c b,Z d.radical c⁆ ⊔ Z d.radical b =
      criticalPlane d.radical c b)
    (hab : Adjacent d.radical (alpha d.radical) b) :
    criticalPlane d.radical c b ≤
      ⁅criticalOrbit d.radical c b,stabilizer d.radical (alpha d.radical)⁆ ⊔
        Z d.radical (alpha d.radical) := by
  rw [←heq]
  apply sup_le_sup
  · apply commutator_mono le_rfl
    exact critical_Z_le_stabilizer d.radical (replacementGeometry h d)
      (alpha d.radical) rfl (by change 0 < replacementDistance h d; omega) hc
  · have hc0 := edge_color hab
    simp only [Z,hc0,Bool.true_eq_false,if_false,edgeOmega]
    exact le_iSup_of_le b (le_iSup_of_le hab le_rfl)

include hl hb hlarge in
/-- Apply both numerical bounds to the actual favorable orientation, and
consume the resulting plane movement in the native full-movement theorem.
The intersection premise is the original PlaneIntersectionInput clause. -/
theorem exists_orderedOrbit_with_full_movement
    (hn : InitialNatural h e hz)
    (hder : ⁅d.radical,d.radical⁆ ≤ pCore 2 d.overgroup)
    (h8 : (omegaCenter d.radical).relIndex
      (replacementMoved d ⊔ omegaCenter d.radical) ≤ 8)
    (h4 : 4 ≤ (omegaCenter d.radical).relIndex
      (⁅d.radical,replacementMoved d⁆ ⊔ omegaCenter d.radical))
    (hinter : ∀ c b, CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl) →
      Adjacent d.radical (alpha d.radical) b → Adjacent d.radical c b →
      ⁅Q d.radical (alpha d.radical),
        Z d.radical c ⊓ Q d.radical (alpha d.radical)⁆ ≤ Z d.radical b) :
    ∃ o : OrderedOrbit (replacementGeometry h d),
      criticalPlane d.radical o.c o.b ≤
        ⁅criticalOrbit d.radical o.c o.b,stabilizer d.radical (alpha d.radical)⁆ ⊔
          Z d.radical (alpha d.radical) ∧
      criticalOrbitNative d.radical o.c o.b =
        ⁅pResidual 2 d.overgroup,criticalOrbitNative d.radical o.c o.b⁆ ⊔
          orbitLayer d.radical := by
  obtain ⟨o⟩ := exists_orderedOrbit (replacementGeometry h d)
    (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)
    hl hb
  have himage := (PairEstimates.source_images_full h e hz hn d hl hb hlarge hder o).2
  have hplane := replacement_plane_eq_of_intersection_bound h e hz d hb hlarge
    o.critical o.adjacent_left o.adjacent_right (hinter _ _ o.critical o.adjacent_left o.adjacent_right)
  have heq := displacement_sup_edge_eq_plane h e hz d hl hb h8 h4
    o.critical o.adjacent_left o.adjacent_right hplane himage
  have hmove := plane_movement h d hb o.critical heq o.adjacent_left
  refine ⟨o,hmove,?_⟩
  exact full_movement_of_plane (replacementGeometry h d) (pResidual 2 d.overgroup)
    (replacement_radical_isPGroup h d) (replacement_residual_sup_radical h d)
    hb o.critical o.adjacent_left o.adjacent_right
    (hl.orbit_core _ _ o.critical o.adjacent_left o.adjacent_right) hmove

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
