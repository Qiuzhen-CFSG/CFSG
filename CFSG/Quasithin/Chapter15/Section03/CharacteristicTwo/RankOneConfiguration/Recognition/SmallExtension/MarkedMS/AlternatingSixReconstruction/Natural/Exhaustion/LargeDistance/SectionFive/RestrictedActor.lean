module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CoreParity
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CoreException

/-!
# The actual reverse even actor and complete radius bounds

Restrict the opposite moved cover using the image of the initial moving
layer U. Reversing the critical pair shows that this image has order at
least four. The restriction therefore controls the radius intersection and
preserves its commutator with U itself. At the reverse endpoint that equality
is an equality of moved subspaces on the original augmentation cover.
`CoreParity` forces an even involution in this same marked reverse image.
This supplies the actual-path consequence needed in (5.2)(i), without
identifying the constructed subgroup with the source's full restricted Z.

The proved radius-image bound and chief-factor dichotomy now give centrality
for both cover orders and every actual radical image. Transport to all
component vertices yields the derived-layer and triple-commutator bounds
of (5.2)(ii)--(iii). The known-simple applications discharge the symmetric
action and central-layer premises and retain the canonical projection.

The terminal distance arguments (5.11)--(5.12), including their shifted-path
and distance-four source constructions, remain with
qt-e-ms-small-a6-exhaustion-large-distance. This does not prove the final
large-distance exclusion.
Source: MS93 (5.0)--(5.2), printed pp.912--915.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CoreCrossing
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
local notation "ρ" => coreRepresentation (Fin 6)

variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

private theorem core_coordinates_moved
    (E : Additive (replacementMoved d) ≃ₗ[ZMod 2] C)
    (hE : ∀ g v, E (coverAction s g v) = ρ g (E v)) (A : Subgroup d.overgroup) :
    (NormalElementaryQuotient.commutatorSpace (replacementMoved d) A).map E.toLinearMap =
      subspaceCommutator ρ ⊤ (A.map s.projection) := by
  let := replacementMoved_normal h d
  rw [NormalElementaryQuotient.commutatorSpace_eq (replacementMoved d) s.projection
    s.surjective (s.projection_kernel.trans (moved_centralizer s).symm)]
  have hh := subspaceCommutator_map_embedding ρ (coverAction s) (MonoidHom.id S)
    E.toLinearMap (fun g v => (hE g v).symm) (A.map s.projection) ⊤
  rw [Submodule.map_top,LinearMap.range_eq_top.mpr E.surjective,Subgroup.map_id] at hh
  exact hh.symm

private theorem core_coordinates_quadratic
    (E : Additive (replacementMoved d) ≃ₗ[ZMod 2] C)
    (hE : ∀ g v, E (coverAction s g v) = ρ g (E v)) (A : Subgroup d.overgroup)
    (hq : ⁅replacementMoved d,A⁆ ≤ centralizer (A : Set d.overgroup)) :
    CoreActor.Quadratic (A.map s.projection) := by
  intro a ha b hb v
  obtain ⟨x,hx,rfl⟩ := ha
  have hmove : ρ b v-v ∈ subspaceCommutator ρ ⊤ (A.map s.projection) :=
    Submodule.subset_span ⟨b,hb,v,Submodule.mem_top,rfl⟩
  rw [←core_coordinates_moved s E hE A] at hmove
  obtain ⟨w,hw,he⟩ := hmove
  rw [←he]
  change ρ (s.projection x) (E w) = E w
  rw [←hE]
  congr 1
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [coverAction_conjugate]
  have hh : x * (w.toMul : d.overgroup) = (w.toMul : d.overgroup) * x := hq hw x hx
  rw [hh,mul_inv_cancel_right]

/-- On the original order-thirty-two cover, preserving the full commutator
of a large quadratic actor forces an actual even involution in its subactor. -/
theorem cover_preserving_actor_even (hcore : Nat.card (replacementMoved d) = 32)
    (A W : Subgroup d.overgroup) [IsElementaryAbelian 2 A]
    (hW : W ≤ A) (hcard : 4 ≤ Nat.card (A.map s.projection))
    (hq : ⁅replacementMoved d,A⁆ ≤ centralizer (A : Set d.overgroup))
    (hpres : ⁅replacementMoved d,W⁆ = ⁅replacementMoved d,A⁆) :
    ∃ a ∈ W.map s.projection, orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  let := replacementMoved_normal h d
  let := IsElementaryAbelian.map (p := 2) (A := A) s.projection
  rcases cover_model s with ⟨E,_⟩ | ⟨E,hE⟩
  · have hc : Nat.card (replacementMoved d) = 16 := by
      change Nat.card (Additive (replacementMoved d)) = 16
      rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,
        finrank_natural_even (Fin 6) (by decide)]
      decide
    omega
  · apply core_preserving_actor_even _ _ (map_mono hW) hcard
      (core_coordinates_quadratic s E hE A hq)
    rw [←core_coordinates_moved s E hE W,←core_coordinates_moved s E hE A]
    congr 1
    unfold NormalElementaryQuotient.commutatorSpace
    rw [hpres]

include s in
/-- The same marked even actor survives every injective endpoint realization. -/
theorem embedded_preserving_actor_even (hcore : Nat.card (replacementMoved d) = 32)
    {H : Type*} [Group H] (i : d.overgroup →* H) (hi : Function.Injective i)
    (A W : Subgroup H) [IsElementaryAbelian 2 A]
    (hA : A ≤ i.range) (hW : W ≤ A)
    (hcard : 4 ≤ ((pCore 2 d.overgroup).map i).relIndex A)
    (hq : ⁅(replacementMoved d).map i,A⁆ ≤ centralizer (A : Set H))
    (hpres : ⁅(replacementMoved d).map i,W⁆ = ⁅(replacementMoved d).map i,A⁆) :
    ∃ a ∈ (W.comap i).map s.projection, orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  let A₀ := A.comap i
  let W₀ := W.comap i
  let := IsElementaryAbelian.comap_of_injective (p := 2) i hi A
  have hmA : A₀.map i = A := map_comap_eq_self hA
  have hmW : W₀.map i = W := map_comap_eq_self (hW.trans hA)
  have hcard₀ : 4 ≤ Nat.card (A₀.map s.projection) := by
    rw [←hmA,relIndex_map_map_of_injective _ _ hi,←s.projection_kernel,relIndex_ker] at hcard
    exact hcard
  apply cover_preserving_actor_even s hcore A₀ W₀ (comap_mono hW) hcard₀
  · intro x hx a ha
    apply hi
    simp only [map_mul]
    apply hq
    · rw [←hmA,←map_commutator]
      exact mem_map_of_mem i hx
    · exact ha
  · apply (map_injective hi)
    rwa [map_commutator,map_commutator,hmA,hmW]

include s in
/-- The actual restricted reverse actor has controlled radius commutators
and contains an even involution in the original marked symmetric quotient.
The restriction retains movement by the initial U, which is stronger than
preserving movement by its full Z-seed alone. -/
theorem critical_radius_restricted_even_actor
    (hc : DistanceTwo.CentralLayer d) (hcore : Nat.card (replacementMoved d) = 32)
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ W : Subgroup (FreeAmalgam d.radical), W ≤ U d.radical a' ∧
      ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ ≤
        Z d.radical (alpha d.radical) ∧
      ∃ a ∈ (W.comap (embedM d.radical)).map s.projection,
        orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  let a := alpha d.radical
  have hl : 2 < p.walk.length := by rw [p.length_eq_b]; exact hb
  let t := p.walk.getVert (p.walk.length-1)
  have hct : Adjacent d.radical a' t := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [p.end_color] at hh
    cases he : color d.radical t <;> simp_all
  have het : Adjacent d.radical (p.walk.getVert (p.walk.length-2)) t := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  let Y := V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2))
  have hYt : Y ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical ht het)
  have hY : Y ≤ stabilizer d.radical a' := fun _ hx =>
    (hYt hx).2 _ (adjacent_symm d.radical hct)
  have hcomm : ⁅U d.radical a',U d.radical a⁆ ≤ ⁅Z d.radical a,Z d.radical a'⁆ := by
    rw [commutator_comm]
    exact commutator_mono (DistanceEight.U_le_Z d.radical a) (DistanceEight.U_le_Z d.radical a')
  have hRZa : ⁅Z d.radical a,Z d.radical a'⁆ ≤ Z d.radical a :=
    ((critical_Z_commutator_le_moving (h:=h) p).trans inf_le_left).trans (DistanceEight.U_le_Z d.radical a)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  let : IsElementaryAbelian 2 (U d.radical a) := IsElementaryAbelian.of_le (DistanceEight.U_le_Z d.radical a)
  have hAA : ⁅U d.radical a',U d.radical a⁆ ≤
      centralizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    (hcomm.trans hRZa).trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le (show (U d.radical a : Set (FreeAmalgam d.radical)) ⊆ Z d.radical a from DistanceEight.U_le_Z d.radical a)))
  have hAY : ⁅U d.radical a',U d.radical a⁆ ≤ centralizer (Y : Set (FreeAmalgam d.radical)) :=
    hcomm.trans (le_centralizer_iff.mp (critical_radius_intersection_centralizes (h:=h) p hb))
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h:=h) hc a' p.end_color
  have hA : U d.radical a ≤ i.range := by
    rw [hir]
    exact (DistanceEight.U_le_Z d.radical a).trans (Z_le_stabilizer_of_dist_le a _ p.critical.1.le)
  have hforwardU := critical_forward_moving_image_four_le s hc p hforward
  obtain ⟨W,hW,_,hpres,hcontrol⟩ := embedded_cover_restriction_preserving s i hi (U d.radical a) hA
    (hiQ.symm ▸ hforwardU) (hiU.symm ▸ hAA)
  have hWU : W ≤ U d.radical a' := hiU ▸ hW
  have hbound : ⁅Y,W⁆ ≤ Z d.radical a := by
    rw [commutator_comm]
    have hh := hcontrol Y (hY.trans_eq hir.symm) (hiU.symm ▸ hAY)
    rw [hiU] at hh
    exact hh.trans (hcomm.trans hRZa)
  have hUbase : U d.radical a' ≤ (embedM d.radical).range := by
    change U d.radical a' ≤ Mbar d.radical
    rw [←stabilizer_m_base d.radical]
    exact (DistanceEight.U_le_Z d.radical a').trans
      (critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical) rfl
        (replacementDistance_pos h d) p.critical)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a' p.end_color
  let : IsElementaryAbelian 2 (U d.radical a') := IsElementaryAbelian.of_le (DistanceEight.U_le_Z d.radical a')
  have hqreverse : ⁅U d.radical a,U d.radical a'⁆ ≤
      centralizer (U d.radical a' : Set (FreeAmalgam d.radical)) :=
    ((commutator_mono (DistanceEight.U_le_Z d.radical a) (DistanceEight.U_le_Z d.radical a')).trans
      ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_right)).trans
        (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hpresreverse : ⁅U d.radical a,W⁆ = ⁅U d.radical a,U d.radical a'⁆ := by
    rw [commutator_comm,commutator_comm (U d.radical a)]
    exact hiU ▸ hpres
  have hr := reverse_critical_moving_image_four_le s hc p hforward
  have hQbase := Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)
  have hU := hc.U_eq_moved
  obtain ⟨c,hcW,hc2,hceven⟩ := embedded_preserving_actor_even s hcore
    (embedM d.radical) (embedM_injective d.radical) (U d.radical a') W hUbase hWU
    (hQbase ▸ hr) (hU ▸ hqreverse) (hU ▸ hpresreverse)
  exact ⟨W,hWU,hbound,c,hcW,hc2,hceven⟩

include s in
/-- MS93 (5.2)(ii) for every original radical image and both central-cover
orders. The exceptional reverse actor is supplied by the actual critical path. -/
theorem radius_commutator_central_general
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d) :
    ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      centralizer (V d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  by_contra hnon
  have hfour := CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive.distance_eq_four_of_radius_commutator_not_central
    d.radical (replacementGeometry h d) hb rfl hnon
  have hcore : Nat.card (replacementMoved d) = 32 := by
    rcases moved_card s with hn | hn
    · exact (hnon (radius_commutator_central_of_natural s hc hn hb)).elim
    · exact hn
  obtain ⟨a',p,hforward⟩ := exists_base_large_critical_path (h := h) (r := d) hfour hnon
  obtain ⟨W,hWU,hcomm,a,haW,ha,heven⟩ := critical_radius_restricted_even_actor s hc hcore hb p hforward
  apply hnon
  apply radius_commutator_central_of_residual_dichotomy (h := h) (r := d) hb
  apply radius_residual_dichotomy_of_index s hb s.surjective
    W (Q d.radical (p.walk.getVert (p.walk.length-2)))
    ((hWU.trans (DistanceEight.U_le_Z d.radical a')).trans
      (critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical) rfl
        (replacementDistance_pos h d) p.critical)) a ha heven haW hcomm
  exact critical_radius_image_index_le_eight_general s hc hb p

/-- The even actor remains in the canonical quotient of the original
minimum characteristic replacement. -/
theorem critical_radius_restricted_even_actor_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hcore : Nat.card (replacementMoved d) = 32)
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hforward : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ W : Subgroup (FreeAmalgam d.radical), W ≤ U d.radical a' ∧
      ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ ≤
        Z d.radical (alpha d.radical) ∧
      ∃ a ∈ (W.comap (embedM d.radical)).map (SourceReduction.projection h e hz hn d),
        orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hh := critical_radius_restricted_even_actor s
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) hcore hb p hforward
  rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hh

include s in
/-- Radius centrality at every component vertex of the original graph. -/
theorem radius_commutator_central_general_at
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (a : Vertex d.radical) (ha : color d.radical a = false) :
    ⁅V d.radical a,Q d.radical a⁆ ≤
      centralizer (V d.radical a : Set (FreeAmalgam d.radical)) := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical ha
  have hV : V d.radical (mVertex d.radical g) =
      (V d.radical (alpha d.radical)).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [alpha,act_mVertex,one_mul] using V_act d.radical g (alpha d.radical)
  have hQ : Q d.radical (mVertex d.radical g) =
      (Q d.radical (alpha d.radical)).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [alpha,act_mVertex,one_mul] using Q_act d.radical g (alpha d.radical)
  rw [hV,hQ,←map_commutator]
  exact (map_mono (radius_commutator_central_general s hc hb)).trans
    (map_centralizer_le_centralizer_image
      (V d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))
      (MulAut.conj g⁻¹).toMonoidHom)

include s in
/-- All radius conclusions of MS93 (5.2)(ii)--(iii), without a condition
on the actual radical image or either central-cover order. -/
theorem radius_bounds_general (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a : Vertex d.radical}
    (ha : color d.radical a = false) (a' c : Vertex d.radical) :
    ⁅V d.radical a,Q d.radical a⁆ ≤ centralizer (V d.radical a : Set (FreeAmalgam d.radical)) ∧
      ⁅V d.radical a,V d.radical a⁆ ≤ X d.radical a ∧
      ⁅⁅X d.radical a' ⊓ Q d.radical a,V d.radical a ⊓ Q d.radical c⁆,
        V d.radical a ⊓ Q d.radical c⁆ = ⊥ := by
  have hcentral := radius_commutator_central_general_at s hc hb a ha
  exact ⟨hcentral,
    CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive.radius_derived_le_X
      d.radical (replacementGeometry h d) hb ha hcentral,
    CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive.critical_radius_triple_commutator
      d.radical hcentral⟩

/-- The original replacement supplies all earlier-source premises of the
radius bounds. The original MS2(a) radical need not be Sylow. -/
theorem radius_bounds_general_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a : Vertex d.radical} (ha : color d.radical a = false) (a' c : Vertex d.radical) :
    ⁅V d.radical a,Q d.radical a⁆ ≤ centralizer (V d.radical a : Set (FreeAmalgam d.radical)) ∧
      ⁅V d.radical a,V d.radical a⁆ ≤ X d.radical a ∧
      ⁅⁅X d.radical a' ⊓ Q d.radical a,V d.radical a ⊓ Q d.radical c⁆,
        V d.radical a ⊓ Q d.radical c⁆ = ⊥ :=
  radius_bounds_general (fullSymmetricAction_knownSimple h e hz hn d hb)
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) hb ha a' c

/-- The original minimum characteristic replacement has central radius
commutators, with the symmetric action and central-layer inputs discharged. -/
theorem radius_commutator_central_general_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d) :
    ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      centralizer (V d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) :=
  radius_commutator_central_general (fullSymmetricAction_knownSimple h e hz hn d hb)
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) hb

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
