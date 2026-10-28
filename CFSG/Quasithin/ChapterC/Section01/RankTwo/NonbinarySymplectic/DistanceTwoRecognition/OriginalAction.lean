module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.MovingFrattini
public import Theory.Representation.SymplecticFourOrthogonalCover.RootNormalizerFixed

/-!
# The original radical action on the full critical displacement

At distance two the full edge has the same image as the opposite critical
Z-layer. When its order is the field order this image has natural displacement
a line. Every two-group in the vertex stabilizer normalizing the edge fixes
the entire covered displacement, by fixed-vector lifting with the complete
kernel retained.

Transporting the original radical restricted to the replacement overgroup
through the literal amalgam embedding applies this to [U,T] = U intersect
Phi(T). In the original ambient group, R normalizes that intersection and
R intersect M fixes it pointwise. The proper nonsylow applications use the
original odd-index witness. They do not prove radical saturation, the unequal
maximal fixed-kernel exclusion, the Sylow comparison or n = 2.
Source: MS93 (3.7), printed pp.872--876.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

open ChapterB.QuasisimpleSource
open Representation Representation.BinaryOffender Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour

/-- Every two-group in the vertex stabilizer normalizing the full edge
centralizes its complete critical displacement. -/
theorem replacement_field_sized_two_normalizer_centralizes
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n)
    (P : Subgroup (stabilizer d.radical a)) (hP : IsPGroup 2 P)
    (hn : P ≤ normalizer ((Q d.radical t).subgroupOf (stabilizer d.radical a) :
      Set (stabilizer d.radical a))) :
    P.map (stabilizer d.radical a).subtype ≤
      centralizer ((⁅Z d.radical a,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)) := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.start_color
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hCtop : replacementComponent d = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 d.overgroup)
    have hh := congrArg (fun A : Subgroup d.overgroup => A.map q)
      (replacement_inner_of_positive h d g (by omega))
    rw [Subgroup.map_sup,show (pCore 2 d.overgroup).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (replacementComponent d) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  have hγker : γ.ker=κ.ker := by
    ext x
    change e.groupEquiv (κC x)=1 ↔ κ x=1
    rw [e.groupEquiv.map_eq_one_iff]
    exact Subtype.ext_iff
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have haq := (replacement_field_sized_edge_factorization h d rev hb hzt hat hsize).1
  have hzq := (replacement_field_sized_edge_factorization h d path hb hat hzt hsize).1
  have hZS : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  let δ := κ.comp (inclusion hZS)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZS κ hκQ).trans (hzq.trans hFc.symm)
  obtain ⟨β,hβcard,hβmark,hβ,hβdim,hβquad⟩ := inner_root_actor_of_field_index rev (by omega)
    (MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) z path.end_color)
    h.nonbinary hFc s e he (replacement_component_image_structure h d).2.2.2.2
    j hj hjr δ (fun x v => hconj (inclusion hZS x) v) hδcard (haq.trans hFc.symm)
  let S := stabilizer d.radical a
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hQS : Q d.radical a ≤ S := fun _ hx => hx.1
  have hjoin := (replacement_field_sized_paired_edges h d path hb hat hzt hsize).1
  have hTS : Q d.radical t ≤ S := by rw [←hjoin]; exact sup_le hQS hZS
  let U₀ := (U d.radical a).subgroupOf S
  let T₀ := (Q d.radical t).subgroupOf S
  let jS := j.codRestrict S (fun w => hUS (hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)))
  have hjSr : jS.range=U₀ := by
    ext x
    constructor
    · rintro ⟨w,rfl⟩
      change j w ∈ U d.radical a
      exact hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)
    · intro hx
      obtain ⟨w,hw⟩ := (show x.val ∈ j.range from hjr.symm ▸ hx)
      exact ⟨w,Subtype.ext hw⟩
  have haction (x : S) (w : s.space.toSubmodule) :
      jS (Multiplicative.ofAdd (MovedSection.coverAction s e (γ x) w)) =
        x*jS (Multiplicative.ofAdd w)*x⁻¹ := by
    apply Subtype.ext
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x w
  have hγβ (x : Z d.radical z) : γ (inclusion hZS x)=β x := by
    exact (congrArg e.groupEquiv
      (show κC (inclusion hZS x)=e.groupEquiv.symm (β x) from
        Subtype.ext (hβmark x).symm)).trans (e.groupEquiv.apply_symm_apply _)
  have hQker : (Q d.radical a).subgroupOf S = γ.ker := by
    rw [hγker,←hκQ,subgroupOf_map_subtype_eq]
  have hZimage : ((Z d.radical z).subgroupOf S).map γ=β.range := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,hγβ ⟨x.val,hx⟩ |>.symm⟩
    · rintro _ ⟨x,rfl⟩
      exact ⟨inclusion hZS x,x.property,hγβ x⟩
  have hTimage : T₀.map γ=β.range := by
    change ((Q d.radical t).subgroupOf S).map γ=β.range
    rw [←hjoin,subgroupOf_sup hQS hZS,Subgroup.map_sup,hQker,
      show γ.ker.map γ=⊥ from (Subgroup.map_eq_bot_iff _).mpr le_rfl,bot_sup_eq,hZimage]
  have hfixed := embedded_two_normalizer_centralizes_displacement U₀ T₀ P hP hn
    (MovedSection.coverProjection s e) he jS hjSr γ haction
    (by rw [hTimage]; exact hβdim.le)
  have hm : (⁅U₀,T₀⁆).map S.subtype=⁅Z d.radical a,Z d.radical z⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hTS]
    exact replacement_field_sized_moving_edge_commutator h d path hb hat hzt hsize
  have hh := (map_mono (f := S.subtype) hfixed).trans
    (map_centralizer_le_centralizer_image _ S.subtype)
  simpa only [←Subgroup.coe_map,hm] using hh

/-- The original radical restricted to the replacement centralizes the
entire moving Frattini intersection, with its fixed attachment included. -/
theorem replacement_field_sized_original_restriction_centralizes
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    R.subgroupOf d.overgroup ≤ centralizer
      ((⁅⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆,d.radical⁆ : Subgroup d.overgroup) :
        Set d.overgroup) := by
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := d.radical) (geometry := g)
    (a := alpha d.radical) rfl
  have hd : (cosetGraph d.radical).dist (alpha d.radical) z = 2 :=
    path.critical.1.trans ((g.distance_constant _ path.start_color).trans hb)
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two d.radical (alpha d.radical) z hd
  have hab : Adjacent d.radical (alpha d.radical) (beta d.radical) :=
    (adjacent_iff_exists_common d.radical _ _).mpr ⟨1,Or.inl ⟨rfl,rfl⟩⟩
  obtain ⟨v,hv,hvt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) hab hat
  let f := (MulAut.conj v⁻¹).toMonoidHom.comp (embedM d.radical)
  have hf : Function.Injective f := (MulAut.conj v⁻¹).injective.comp (embedM_injective d.radical)
  have hmT : d.radical.map f=Q d.radical t := by
    dsimp only [f]
    rw [←Subgroup.map_map,←Q_beta,←Q_act,hvt]
  have hmU : (⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆).map f =
      U d.radical (alpha d.radical) := by
    dsimp only [f]
    rw [←Subgroup.map_map,←core_alpha d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_residual h d),
      replacement_core_eq_U_of_distance_two h d g hb rfl,←U_act,hv]
  let S := stabilizer d.radical (alpha d.radical)
  have hfr : f.range=S := by
    dsimp only [f,S]
    rw [MonoidHom.range_comp,show (embedM d.radical).range=stabilizer d.radical (alpha d.radical)
      from (stabilizer_m_base d.radical).symm,←stabilizer_act,hv]
  let B := (R.subgroupOf d.overgroup).map f
  have hBS : B ≤ S := hfr ▸ map_le_range f _
  have hBN : B ≤ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [←hmT]
    apply (map_mono (f := f) ?_).trans (d.radical.le_normalizer_map f)
    let := d.characteristic
    have hR := R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R d.subgroup)
    intro x hx
    apply mem_normalizer_iff.mpr
    intro y
    exact mem_normalizer_iff.mp (hR hx) y.val
  let P := B.subgroupOf S
  have hP : IsPGroup 2 P := ((h.radical.isPGroup.comap_subtype (K := d.overgroup)).map f).of_equiv
    (subgroupOfEquivOfLe hBS).symm
  have hPn : P ≤ normalizer ((Q d.radical t).subgroupOf S : Set S) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro y
    exact mem_normalizer_iff.mp (hBN hx) y.val
  have hc := replacement_field_sized_two_normalizer_centralizes h d path hb hat hzt hsize P hP hPn
  rw [map_subgroupOf_eq_of_le hBS,
    ←replacement_field_sized_moving_edge_commutator h d path hb hat hzt hsize,
    ←hmU,←hmT,←map_commutator] at hc
  intro x hx y hy
  apply hf
  simpa only [map_mul] using hc (mem_map_of_mem f hx) (f y) (mem_map_of_mem f hy)

/-- The original odd-index witness discharges the field-sized premise for
the complete original-radical action. -/
theorem replacement_proper_nonsylow_original_restriction_centralizes
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    R.subgroupOf d.overgroup ≤ centralizer
      ((⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆ ⊓
        (frattini d.radical).map d.radical.subtype : Subgroup d.overgroup) : Set d.overgroup) := by
  have hs := replacement_proper_nonsylow_card h d g hb hnsyl hne
  rw [replacement_field_sized_moving_inf_radical_frattini h d g hb hs]
  exact replacement_field_sized_original_restriction_centralizes h d g hb hs

/-- In the original ambient group the full radical normalizes the moving
Frattini intersection, and its intersection with the replacement fixes it
pointwise. Both assertions use the original odd-index witness. -/
theorem replacement_proper_nonsylow_original_action
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    let W := (blockU K).map K.subtype ⊓ (frattini d.ambient).map d.ambient.subtype
    R ≤ normalizer (W : Set H) ∧ R ⊓ d.overgroup ≤ centralizer (W : Set H) := by
  refine ⟨(replacement_proper_nonsylow_original_frattini_action h d g hb hnsyl hne).2,?_⟩
  let := h.component_normal
  have hperfect : IsPPerfect 2 K := by
    rw [←h.residual_eq]
    exact isPPerfect_pResidual 2
  have hmU := d.commutatorCore_eq_intrinsic_of_sup (original_sup h) hperfect
  have hmT : d.radical.map d.overgroup.subtype=d.ambient := map_subgroupOf_eq_of_le le_sup_right
  have hm : (⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆ ⊓
      (frattini d.radical).map d.radical.subtype).map d.overgroup.subtype =
      (blockU K).map K.subtype ⊓ (frattini d.ambient).map d.ambient.subtype := by
    rw [map_inf _ _ _ d.overgroup.subtype_injective,hmU,
      ←frattini_image_map _ _ d.overgroup.subtype_injective,hmT]
  have hh := (map_mono (f := d.overgroup.subtype)
    (replacement_proper_nonsylow_original_restriction_centralizes h d g hb hnsyl hne)).trans
      (map_centralizer_le_centralizer_image _ d.overgroup.subtype)
  simpa only [←Subgroup.coe_map,hm,subgroupOf_map_subtype,inf_comm] using hh

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
