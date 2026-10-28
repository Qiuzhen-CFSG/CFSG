module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.FixedFrattini
public import Theory.Frattini.Intersection

/-!
# The moving part of the full replacement Frattini subgroup

In the field-sized branch write W for the common critical displacement.
The established formula Phi(T) = Phi(Q) W retains the entire fixed factor.
Its intersection with U is nevertheless exactly W: U intersect Phi(Q)
lies in the full fixed kernel, which is already contained in W. Also
W = [U,T]. Transport through the injective free-amalgam coordinates gives
the same identity for the literal replacement radical, and preservation
of the intrinsic component core gives it in the original ambient group.

The original radical normalizes both the characteristic replacement and
the intrinsic component core, hence also this displacement. The final
application obtains the field-sized premise from the ORIGINAL odd-index
witness. No fixed factor is discarded and no radical equality is inferred.
Source: MS93 (3.7), printed pp.872--876.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition

private theorem inf_sup_eq_of_intersection_le {G : Type*} [Group G]
    (U P W : Subgroup G) (hWU : W ≤ U) (hPU : U ⊓ P ≤ W)
    (hn : P ≤ normalizer (W : Set G)) : U ⊓ (P ⊔ W) = W := by
  apply le_antisymm _ (le_inf hWU le_sup_right)
  intro x hx
  have hp : x ∈ (P ⊔ W : Subgroup G) := hx.2
  rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _ hn] at hp
  obtain ⟨p,hp,w,hw,he⟩ := hp
  have hpu : p ∈ U := by
    have hh := U.mul_mem hx.1 (U.inv_mem (hWU hw))
    simpa only [←he,mul_inv_cancel_right] using hh
  exact he ▸ W.mul_mem (hPU ⟨hpu,hp⟩) hw

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The whole moving core meets the full edge Frattini subgroup in exactly
the common critical displacement. The fixed Frattini factor is retained. -/
theorem replacement_field_sized_moving_inf_edge_frattini
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    U d.radical a ⊓ (frattini (Q d.radical t)).map (Q d.radical t).subtype =
      ⁅Z d.radical a,Z d.radical z⁆ := by
  obtain ⟨_,hAW,hWU,_,_⟩ := replacement_field_sized_paired_fixed_layers h d path hb hat hzt hsize
  have hP := replacement_field_sized_frattini_le_fixedCore h d path hb hat hzt hsize
  rw [replacement_field_sized_edge_frattini h d path hb hat hzt hsize]
  apply inf_sup_eq_of_intersection_le _ _ _ (hWU.trans inf_le_left)
  · intro x hx
    exact hAW (mem_sup_left ⟨hx.1,(hP hx.2).2⟩)
  · have hPQ : (frattini (Q d.radical a)).map (Q d.radical a).subtype ≤ Q d.radical a :=
      map_subtype_le _
    have hWZ := hWU.trans inf_le_left |>.trans (U_le_Z a)
    exact (hPQ.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a path.start_color)))).trans
      ((centralizer_le hWZ).trans (Subgroup.centralizer_le_normalizer _))

/-- The same displacement is the action of the entire edge on the moving core. -/
theorem replacement_field_sized_moving_edge_commutator
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    ⁅U d.radical a,Q d.radical t⁆ = ⁅Z d.radical a,Z d.radical z⁆ := by
  rw [replacement_field_sized_displacement_eq_moving h d path hb hat hzt hsize]
  have hjoin := (replacement_field_sized_paired_edges h d path hb hat hzt hsize).1
  apply le_antisymm _ (commutator_mono le_rfl (le_sup_right.trans_eq hjoin))
  apply commutator_le_moving_of_inner_mod_centralizer
    (U d.radical a) (Z d.radical z) (Q d.radical t)
    (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_reverse_actor_normalizes_moving path)
  rw [←hjoin]
  apply sup_le _ le_sup_left
  apply le_sup_right.trans' ?_
  exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (Z_centralizes_Q d.radical a path.start_color))).trans
      (centralizer_le (U_le_Z a))

/-- On the literal replacement the intrinsic moving core has exact
Frattini intersection, rather than just an identity modulo fixed vectors. -/
theorem replacement_field_sized_moving_inf_radical_frattini
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    ⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆ ⊓
        (frattini d.radical).map d.radical.subtype =
      ⁅⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆,d.radical⁆ := by
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
  have hmT : d.radical.map f = Q d.radical t := by
    dsimp only [f]
    rw [←Subgroup.map_map,←Q_beta,←Q_act,hvt]
  have hmU : (⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆).map f =
      U d.radical (alpha d.radical) := by
    dsimp only [f]
    rw [←Subgroup.map_map,←core_alpha d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_residual h d),
      replacement_core_eq_U_of_distance_two h d g hb rfl,←U_act,hv]
  apply map_injective hf
  rw [map_inf _ _ _ hf,hmU,map_commutator,hmU,hmT,
    ←frattini_image_map d.radical f hf,hmT]
  rw [replacement_field_sized_moving_inf_edge_frattini h d path hb hat hzt hsize,
    replacement_field_sized_moving_edge_commutator h d path hb hat hzt hsize]

/-- The same exact intersection in the ORIGINAL ambient group, on its
preserved intrinsic component core. -/
theorem replacement_field_sized_original_moving_inf_frattini
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    (blockU K).map K.subtype ⊓ (frattini d.ambient).map d.ambient.subtype =
      ⁅(blockU K).map K.subtype,d.ambient⁆ := by
  let := h.component_normal
  have hperfect : IsPPerfect 2 K := by
    rw [←h.residual_eq]
    exact isPPerfect_pResidual 2
  have hmU := d.commutatorCore_eq_intrinsic_of_sup (original_sup h) hperfect
  have hmT : d.radical.map d.overgroup.subtype = d.ambient :=
    map_subgroupOf_eq_of_le le_sup_right
  have hh := congrArg (fun A : Subgroup d.overgroup => A.map d.overgroup.subtype)
    (replacement_field_sized_moving_inf_radical_frattini h d g hb hsize)
  rw [map_inf _ _ _ d.overgroup.subtype_injective,hmU,map_commutator,hmU,hmT,
    ←frattini_image_map _ _ d.overgroup.subtype_injective,hmT] at hh
  exact hh

omit [Finite F] [CharP F 2] in
/-- The ORIGINAL radical acts on the actual displacement, since it preserves
both the component core and its characteristic replacement. -/
theorem original_radical_normalizes_replacement_displacement :
    R ≤ normalizer ((⁅(blockU K).map K.subtype,d.ambient⁆ : Subgroup H) : Set H) := by
  let := h.component_normal
  let := d.characteristic
  have hU : R ≤ normalizer ((blockU K).map K.subtype : Set H) := by
    apply le_trans (show R ≤ normalizer (K : Set H) by rw [normalizer_eq_top]; exact le_top)
    exact normalizer_le_normalizer_characteristic_image K (blockU K)
  have hT : R ≤ normalizer (d.ambient : Set H) :=
    R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R d.subgroup)
  intro r hr
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hU hr),
    mem_normalizer_iff_map_conj_eq.mp (hT hr)]

/-- Original odd-index witness application: the moving Frattini intersection
is the full critical displacement and is preserved by the ORIGINAL radical. -/
theorem replacement_proper_nonsylow_original_frattini_action
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    let W := (blockU K).map K.subtype ⊓ (frattini d.ambient).map d.ambient.subtype
    W = ⁅(blockU K).map K.subtype,d.ambient⁆ ∧ R ≤ normalizer (W : Set H) := by
  have hs := replacement_proper_nonsylow_card h d g hb hnsyl hne
  have he := replacement_field_sized_original_moving_inf_frattini h d g hb hs
  exact ⟨he,he.symm ▸ original_radical_normalizes_replacement_displacement h d⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
