module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Intersection.Model
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Structure.Transposition.Source

/-!
# The complete opposite-plane bound for an elementary edge image

Use the literal opposite-edge coordinates and the critical transposition.
The part of the opposite Z-layer inside the initial two-core centralizes the
initial Z-layer. Separate its central edge seed and apply the whole-cover
fixed-hyperplane calculation to its moving part. Every resulting displacement
is fixed by the entire radical image and hence belongs to the original edge
omega center. The unique common neighbor identifies the supplied path with
the coordinate witness's path.

This proves the exact plane-intersection bound, its maximal-plane equality,
and all local calculations when the actual radical image is elementary.
Assembly.Intersection.Source applies these to whole-core exhaustion.
Constructing that image from the original source assumptions remains with
qt-e-ms-small-a6-exhaustion-distance-two. No natural subgroup complement or
Sylow hypothesis is used. Source: MS93 (3.6), printed p.871.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Intersection
open LocalImages LargeDistance PlaneMovement
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)

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
/-- An elementary literal radical image supplies the complete opposite-plane
bound, including the fixed central attachment of the order-thirty-two cover. -/
theorem plane_intersection_of_elementary_image
    (hel : IsElementaryAbelian 2 (d.radical.map (Recognition.sourceProjection h e hz hn d)))
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    {c b : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl))
    (hab : Adjacent d.radical (alpha d.radical) b) (hcb : Adjacent d.radical c b) :
    ⁅Q d.radical (alpha d.radical),Z d.radical c ⊓ Q d.radical (alpha d.radical)⁆ ≤
      Z d.radical b := by
  obtain ⟨b',i,A,hi,hab',hcb',hAR,hAm,hiW,hiS,hiL,hiR,t,ht,hAt⟩ :=
    critical_transposition_coordinates_with_edge h e hz hn d hb hlarge hc
  have hac : alpha d.radical ≠ c := by
    intro hh
    have hd := hc.1.trans hb
    rw [hh,SimpleGraph.dist_self] at hd
    omega
  have hbb := common_neighbor_unique d.radical hac hab hcb hab' hcb'
  subst b'
  let := replacementMoved_normal h d
  let := moved_elementary h d
  let W := replacementMoved d
  let q := Recognition.sourceProjection h e hz hn d
  let B := d.radical.map q
  let : IsElementaryAbelian 2 B := hel
  have hq := sourceProjection_surjective_of_nonfrattini h e hz hn d hb hlarge
  let hk := (Recognition.sourceProjection_kernel h e hz hn d).trans
    (moved_centralizer h e hz hn d).symm
  let ρ := NormalElementaryQuotient.representation W q hq hk
  have hmodel := moved_cover_model h e hz hn d hq
  have htB : t ∈ B := map_mono hAR (hAt ▸ mem_zpowers t)
  have hZc : Z d.radical c = (W ⊔ omegaCenter d.radical).map i := by
    rw [Subgroup.map_sup,hiW,hiS]
    exact CentralLayer.Z_eq_moving_sup_edge_at h e hz d
      (critical_endpoint_color d.radical (alpha d.radical) rfl _ hc) hcb
  have hQa : Q d.radical (alpha d.radical) ≤ d.radical.map i := by
    rw [hiR]
    exact Q_le_adjacent_h d.radical (DistanceTwo.NaturalCore.edge_color hab) hab
  have hWR : W ≤ d.radical := (replacementMoved_le_omegaCenter h d).trans
    ((omegaCenter_le _).trans (replacement_core_le_radical h d))
  apply commutator_le.mpr
  intro y hy z hzI
  obtain ⟨y,hyR,rfl⟩ := hQa hy
  obtain ⟨z,hz,rfl⟩ := hZc.le hzI.1
  obtain ⟨w,hw,s,hs,rfl⟩ := mem_sup_of_normal_left.mp hz
  have hsA : s ∈ centralizer (A : Set d.overgroup) := by
    intro a ha
    exact (mem_omegaCenter_iff.mp hs).2.2 a (hAR ha)
  have hzA : w*s ∈ centralizer (A : Set d.overgroup) := by
    intro a ha
    apply hi
    simp only [map_mul]
    simpa only [map_mul] using (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical (alpha d.radical) rfl)
      (hAm ▸ mem_map_of_mem i ha) _ hzI.2).symm
  have hwA : w ∈ centralizer (A : Set d.overgroup) := by
    simpa only [mul_inv_cancel_right] using
      (centralizer (A : Set d.overgroup)).mul_mem hzA
        ((centralizer (A : Set d.overgroup)).inv_mem hsA)
  let w0 : Additive W := Additive.ofMul ⟨w,hw⟩
  have hwt : ρ t w0 = w0 := by
    obtain ⟨a,ha,hat⟩ := hAt.ge (mem_zpowers t)
    rw [←hat]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [NormalElementaryQuotient.representation_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (hwA a ha)
  let v := ρ (q y) w0 - w0
  have hvval : (v.toMul : d.overgroup) = ⁅y,w⁆ := by
    dsimp only [v]
    rw [toMul_sub,div_eq_mul_inv]
    change ((ρ (q y) w0).toMul : d.overgroup) * w⁻¹ = _
    rw [NormalElementaryQuotient.representation_apply]
    rfl
  have hvC : (v.toMul : d.overgroup) ∈ centralizer (d.radical : Set d.overgroup) := by
    intro r hr
    have hvf : ρ (q r) v = v := elementary_cover_fixed_displacement ρ hmodel B t ht htB
      (q y) (mem_map_of_mem q hyR) (q r) (mem_map_of_mem q hr) w0 hwt
    have he := congrArg (fun x : Additive W => (x.toMul : d.overgroup)) hvf
    rw [NormalElementaryQuotient.representation_apply] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hvS : (v.toMul : d.overgroup) ∈ omegaCenter d.radical :=
    mem_omegaCenter_iff.mpr ⟨hWR v.toMul.property,
      elemPow_eq_one_of_isElementaryAbelian (p := 2) _ v.toMul.property,hvC⟩
  have hys : Commute (i y) (i s) := by
    change i y * i s = i s * i y
    simpa only [map_mul] using congrArg i ((mem_omegaCenter_iff.mp hs).2.2 y hyR)
  rw [map_mul,commutatorElement_mul_right_eq_mul_conj,hys.commutator_eq]
  simp only [mul_one,mul_inv_cancel_right]
  rw [←map_commutatorElement,←hvval,←hiS]
  exact mem_map_of_mem i hvS

include h e hz hn in
/-- Literal maximal-plane identity obtained from the whole-cover action. -/
theorem plane_eq_of_elementary_image
    (hel : IsElementaryAbelian 2 (d.radical.map (Recognition.sourceProjection h e hz hn d)))
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    {c b : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c
      ((replacementGeometry h d).exists_critical _ rfl))
    (hab : Adjacent d.radical (alpha d.radical) b) (hcb : Adjacent d.radical c b) :
    criticalPlane d.radical c b = Z d.radical c ⊓ Q d.radical (alpha d.radical) :=
  replacement_plane_eq_of_intersection_bound h e hz d hb hlarge hc hab hcb
    (plane_intersection_of_elementary_image h e hz hn d hel hb hlarge hc hab hcb)

include h e hz hn in
/-- All original local calculations now follow from the concrete elementary
radical image, with no independent plane-intersection input. -/
theorem localCalculations_of_elementary_image
    (hel : IsElementaryAbelian 2 (d.radical.map (Recognition.sourceProjection h e hz hn d)))
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) :
    LocalCalculations d.radical (replacementGeometry h d) :=
  localCalculations_of_intersection_bound h e hz hn d hb hlarge
    (fun _ _ hc hab hcb => plane_intersection_of_elementary_image h e hz hn d hel hb hlarge hc hab hcb)

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Intersection
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
