module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.NormalizerComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.WholeKernel
public import Theory.Frattini.QuadraticCentralizer
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The full saturated radical in both endpoint quotients

Saturation identifies the replacement image with the two-core of its own
normalizer. Thus the point, plane and Sylow alternatives concern that image
itself. Edge coordinates then transport the original component marking to
every incident endpoint, with the entire edge radical and exact two-core
kernel retained. Both ends of a distance-two critical pair consequently
act through the same marked full radical.

This is preparation for MS93 (3.7), printed pp.872--877; it does not yet
prove the field restriction or discard any component-fixed attachment.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition Theory.SpecificGroups.SymplecticFour
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

/-- The conditional saturation premise holds on the exact original marked image. -/
theorem marked_radical_saturated
    (g : Geometry d.radical) (hb : 0 < g.b d.radical)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical) :
    (normalizer ((d.ambient.subgroupOf K).map (componentProjection h) :
      Set (Sp F))).pCoreIn 2 = (d.ambient.subgroupOf K).map (componentProjection h) := by
  obtain ⟨f,hf,hk,_,he⟩ := exists_replacement_marked_projection h d g hb
  have hh := (replacement_radical_saturation_iff h d f hf hk).mp hsat
  rwa [he] at hh

/-- These are alternatives for D itself, with the same conjugator on its
normalizer, rather than alternatives for a possibly larger O₂(N(D)). -/
theorem marked_radical_alternatives
    (g : Geometry d.radical) (hb : 0 < g.b d.radical)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical) :
    let D := (d.ambient.subgroupOf K).map (componentProjection h)
    (∃ u : Sp F,
      (D.map (MulAut.conj u).toMonoidHom = pointRadicalAmbient ∧
        (normalizer (D : Set (Sp F))).map (MulAut.conj u).toMonoidHom = pointParabolic) ∨
      (D.map (MulAut.conj u).toMonoidHom = planeRadicalAmbient ∧
        (normalizer (D : Set (Sp F))).map (MulAut.conj u).toMonoidHom = planeParabolic)) ∨
    ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) = D := by
  have hh := replacement_marked_normalizer_core_alternatives h d g hb
  rwa [marked_radical_saturated h d g hb hsat] at hh

/-- The actual saturated radical quotient has order q³ or q⁴. In particular,
the order-q replacement lemmas are not applicable to this branch. -/
theorem marked_radical_card
    (g : Geometry d.radical) (hb : 0 < g.b d.radical)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical) :
    Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = Nat.card F^3 ∨
      Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = Nat.card F^4 := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  rcases marked_radical_alternatives h d g hb hsat with ⟨u,hu⟩ | ⟨S,hS⟩
  · left
    have hc := card_map_of_injective (f := (MulAut.conj u).toMonoidHom) (K := (d.ambient.subgroupOf K).map
      (componentProjection h)) (MulAut.conj u).injective
    rw [←hc]
    rcases hu with ⟨he,_⟩ | ⟨he,_⟩
    · rw [he]
      exact SymplecticConjugatePair.card_pointRadical
    · rw [he]
      exact SymplecticConjugatePair.card_planeRadical
  · right
    obtain ⟨u,hu⟩ := MulAction.exists_smul_eq (Sp F) S
      (unipotentSylow h.field_card (by have := h.nonbinary; omega))
    have he : (S : Subgroup (Sp F)).map (MulAut.conj u).toMonoidHom = unipotent :=
      congrArg Sylow.toSubgroup hu
    have hc := congrArg (fun A : Subgroup (Sp F) => Nat.card A) he
    rw [card_map_of_injective (MulAut.conj u).injective,hS] at hc
    exact hc.trans card_unipotent

/-- Coordinates simultaneously aligned with an endpoint and its incident
full radical. The component equation retains the original quotient marking. -/
structure EdgeMarking (a t : Vertex d.radical) where
  embedding : d.overgroup →* FreeAmalgam d.radical
  injective : Function.Injective embedding
  range_eq : embedding.range = stabilizer d.radical a
  core_eq : (pCore 2 d.overgroup).map embedding = Q d.radical a
  radical_eq : d.radical.map embedding = Q d.radical t
  residual_eq : (K.subgroupOf d.overgroup).map embedding = Ltilde d.radical a
  quotient : stabilizer d.radical a →* Sp F
  onto : Function.Surjective quotient
  kernel : quotient.ker.map (stabilizer d.radical a).subtype = Q d.radical a
  radical_image : ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map quotient =
    (d.ambient.subgroupOf K).map (componentProjection h)
  component_equation : ∀ k : K.subgroupOf d.overgroup,
    quotient ⟨embedding k,range_eq ▸ (show embedding k ∈ embedding.range from ⟨k,rfl⟩)⟩ =
      componentProjection h (subgroupOfEquivOfLe le_sup_left k)

/-- Construct the same literal component and radical marking at any oriented edge. -/
theorem exists_edgeMarking
    (g : Geometry d.radical) (hb : 0 < g.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) : Nonempty (EdgeMarking h d a t) := by
  obtain ⟨u,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  swap
  · cases ha
  let i := (MulAut.conj u⁻¹).toMonoidHom.comp (embedM d.radical)
  have hi : Function.Injective i := (MulAut.conj u⁻¹).injective.comp (embedM_injective d.radical)
  have ha : act d.radical u (alpha d.radical) = mVertex d.radical u := by
    simp only [alpha,act_mVertex,one_mul]
  have ht : act d.radical u (beta d.radical) = hVertex d.radical u := by
    simp only [beta,act_hVertex,one_mul]
  have hir : i.range = stabilizer d.radical (mVertex d.radical u) := by
    dsimp only [i]
    rw [MonoidHom.range_comp]
    change (Mbar d.radical).map (MulAut.conj u⁻¹).toMonoidHom = _
    rw [←stabilizer_m_base,←stabilizer_act,act_mVertex,one_mul]
  have hiQ : (pCore 2 d.overgroup).map i = Q d.radical (mVertex d.radical u) := by
    dsimp only [i]
    rw [←map_map,←Q_alpha d.radical (replacement_isPGroup h d)
      (replacement_core_le h d),←Q_act,ha]
  have hiT : d.radical.map i = Q d.radical (hVertex d.radical u) := by
    dsimp only [i]
    rw [←map_map,←Q_beta,←Q_act,ht]
  have hiL : (K.subgroupOf d.overgroup).map i = Ltilde d.radical (mVertex d.radical u) := by
    dsimp only [i]
    rw [←map_map,←replacement_residual h d,←Ltilde_alpha,←Ltilde_act,ha]
  obtain ⟨f,hf,hk,hm,he⟩ := exists_replacement_marked_projection h d g hb
  let κ := ElementaryMovedCover.embeddedQuotient f i hi _ hir
  refine ⟨{
    embedding := i
    injective := hi
    range_eq := hir
    core_eq := hiQ
    radical_eq := hiT
    residual_eq := hiL
    quotient := κ
    onto := ElementaryMovedCover.embeddedQuotient_surjective f i hi _ hir hf
    kernel := ?_
    radical_image := ?_
    component_equation := ?_ }⟩
  · rw [ElementaryMovedCover.embeddedQuotient_kernel,hk,hiQ]
  · rw [←hiT,ElementaryMovedCover.embeddedQuotient_subgroup,he]
  · intro k
    let e := (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hir)
    change f (e.symm (e k)) = _
    rw [e.symm_apply_apply]
    exact hm k


namespace EdgeMarking
variable {h d} {a z t : Vertex d.radical} (c : EdgeMarking h d a t)
include c

omit [Finite H] [Finite F] [CharP F 2] in
/-- The marked full radical is contained in the actual endpoint stabilizer. -/
theorem edge_le : Q d.radical t ≤ stabilizer d.radical a := by
  rw [←c.radical_eq,←c.range_eq]
  exact map_le_range _ _

omit [Finite F] [CharP F 2] in
/-- The entire endpoint kernel is contained in the same full radical. -/
theorem core_le_edge : Q d.radical a ≤ Q d.radical t := by
  rw [←c.core_eq,←c.radical_eq]
  exact map_mono (replacement_core_le h d)

omit [Finite H] [Finite F] [CharP F 2] in
/-- The action of the whole edge radical in the supplied original field. -/
@[expose] def action : Q d.radical t →* Sp F :=
  c.quotient.comp (inclusion c.edge_le)

omit [Finite H] [Finite F] [CharP F 2] in
/-- The whole actor image, not merely an elementary critical subactor. -/
theorem action_range : c.action.range =
    (d.ambient.subgroupOf K).map (componentProjection h) := by
  rw [action,MonoidHom.range_comp,inclusion_range,c.radical_image]

omit [Finite H] [Finite F] [CharP F 2] in
/-- Its kernel is the entire endpoint two-core restricted to the common actor. -/
theorem action_kernel : c.action.ker = (Q d.radical a).subgroupOf (Q d.radical t) := by
  have hk : c.quotient.ker = (Q d.radical a).subgroupOf (stabilizer d.radical a) := by
    rw [←c.kernel,subgroupOf_map_subtype_eq]
  rw [action,←MonoidHom.comap_ker,hk,comap_inclusion_subgroupOf]

/-- Saturation is preserved by these literal endpoint coordinates. -/
theorem action_saturated
    (g : Geometry d.radical) (hb : 0 < g.b d.radical)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical) :
    (normalizer (c.action.range : Set (Sp F))).pCoreIn 2 = c.action.range := by
  rw [c.action_range]
  exact marked_radical_saturated h d g hb hsat

omit [Finite H] [Finite F] [CharP F 2] in
/-- The common action has the literal intersection of both complete cores
as kernel; no fixed attachment is factored out of the edge in advance. -/
theorem paired_action_kernel (c' : EdgeMarking h d z t) :
    (c.action.prod c'.action).ker =
      (Q d.radical a ⊓ Q d.radical z).subgroupOf (Q d.radical t) := by
  ext x
  change (c.action x,c'.action x) = (1,1) ↔ _
  rw [Prod.mk.injEq]
  change (x ∈ c.action.ker ∧ x ∈ c'.action.ker) ↔ _
  rw [c.action_kernel,c'.action_kernel]
  rfl

omit [Finite H] [Finite F] [CharP F 2] in
/-- Each complete core is normal in the common radical. -/
theorem core_normal : ((Q d.radical a).subgroupOf (Q d.radical t)).Normal := by
  rw [←c.action_kernel]
  infer_instance

omit [Finite H] [Finite F] [CharP F 2] in
/-- The same original-field image occurs on both sides of the critical pair. -/
theorem paired_action_ranges (c' : EdgeMarking h d z t) :
    c.action.range = c'.action.range := c.action_range.trans c'.action_range.symm

/-- At positive distance, the entire endpoint is its residual times its
core, in the same edge-aligned coordinates. -/
theorem residual_sup_core
    (g : Geometry d.radical) (hb : 0 < g.b d.radical) :
    Ltilde d.radical a ⊔ Q d.radical a = stabilizer d.radical a := by
  rw [←c.residual_eq,←c.core_eq,←Subgroup.map_sup,
    replacement_inner_of_positive h d g hb,←MonoidHom.range_eq_map,c.range_eq]

end EdgeMarking

/-- Both full radical actions are constructed on one actual distance-two
critical configuration, using one field and the original quotient marking.
The classified subgroup in each action is the whole common actor image. -/
theorem exists_paired_full_radical_actions
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical) :
    ∃ (z t : Vertex d.radical) (_path : CriticalPath d.radical g (alpha d.radical) z),
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical z t ∧
      ∃ (c : EdgeMarking h d (alpha d.radical) t) (c' : EdgeMarking h d z t),
        c.action.range = c'.action.range ∧
        (normalizer (c.action.range : Set (Sp F))).pCoreIn 2 = c.action.range ∧
        (normalizer (c'.action.range : Set (Sp F))).pCoreIn 2 = c'.action.range ∧
        (c.action.prod c'.action).ker =
          (Q d.radical (alpha d.radical) ⊓ Q d.radical z).subgroupOf (Q d.radical t) ∧
        (Nat.card c.action.range = Nat.card F^3 ∨
          Nat.card c.action.range = Nat.card F^4) := by
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := d.radical) (geometry := g)
    (a := alpha d.radical) rfl
  have hd : (cosetGraph d.radical).dist (alpha d.radical) z = 2 :=
    path.critical.1.trans ((g.distance_constant _ path.start_color).trans hb)
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two d.radical (alpha d.radical) z hd
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  refine ⟨z,t,path,hat,hzt,c,c',c.paired_action_ranges c',
    c.action_saturated g (by omega) hsat,c'.action_saturated g (by omega) hsat,
    c.paired_action_kernel c',?_⟩
  rw [c.action_range]
  exact marked_radical_card h d g (by omega) hsat


include h

/-- Source (3.6)'s Frattini fixedness holds for the entire local two-core
at every vertex, independently of the size of the replacement image. -/
theorem frattini_le_fixedCore
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a : Vertex d.radical} (ha : color d.radical a = false) :
    (frattini (Q d.radical a)).map (Q d.radical a).subtype ≤ fixedCore d.radical a := by
  let := finite_stabilizer d.radical a
  let : Finite (Q d.radical a) := Finite.of_injective
    (inclusion (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1))
    (inclusion_injective _)
  let : IsElementaryAbelian 2 (U d.radical a) := replacement_vertex_moving_elementary h d ha
  have hmove : ⁅Q d.radical a,Ltilde d.radical a⁆ ≤ U d.radical a :=
    (replacement_core_eq_U_of_distance_two h d g hb ha).le
  have hc : U d.radical a ≤ centralizer (Q d.radical a : Set (FreeAmalgam d.radical)) :=
    (U_le_Z a).trans (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha))
  exact le_inf (map_subtype_le _) (frattini_image_le_centralizer_of_elementary_commutator
    (Q d.radical a) (Ltilde d.radical a) (U d.radical a)
    (Q_isPGroup d.radical (replacement_isPGroup h d) (replacement_core_le h d) a ha)
    hmove (le_centralizer_iff.mp hc))

/-- The full edge acts trivially on the entire fixed attachment modulo
Φ(Q). This uses the full residual/core product, not an elementary quotient
substitute for the attachment itself. -/
theorem fixedCore_displacement_le_frattini
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (c : EdgeMarking h d a t) :
    ⁅fixedCore d.radical a,Q d.radical t⁆ ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype := by
  let := finite_stabilizer d.radical a
  let : Finite (Q d.radical a) := Finite.of_injective
    (inclusion (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1))
    (inclusion_injective _)
  let : Fact (IsPGroup 2 (Q d.radical a)) := ⟨Q_isPGroup d.radical
    (replacement_isPGroup h d) (replacement_core_le h d) a ha⟩
  have hder : ⁅Q d.radical a,Q d.radical a⁆ ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype := by
    have hh := map_mono (f := (Q d.radical a).subtype)
      (commutator_le_frattini_of_isPGroup (R := Q d.radical a) (p := 2))
    simpa only [commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hh
  have hnorm := (Q_normalized d.radical a).trans
    (normalizer_le_normalizer_characteristic_image (Q d.radical a) (frattini (Q d.radical a)))
  have hcentral : ⁅Ltilde d.radical a,fixedCore d.radical a⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  rw [commutator_comm]
  apply (commutator_mono c.edge_le le_rfl).trans
  rw [←c.residual_sup_core g (by omega)]
  exact commutator_sup_le_of_relative_normal (stabilizer d.radical a)
    (Ltilde d.radical a) (Q d.radical a) (fixedCore d.radical a) _
    hnorm (Ltilde_le_stabilizer _) (fun _ hx => hx.1)
    (hcentral.le.trans bot_le) ((commutator_mono le_rfl inf_le_left).trans hder)

/-- Both complete fixed attachments carry actions of the same full radical;
each displacement lies in its own Frattini subgroup and remains fixed by
its whole component. No equality or vanishing of the attachments is asserted. -/
theorem paired_fixedCore_displacement
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t) :
    ⁅fixedCore d.radical a,Q d.radical t⁆ ≤
        (frattini (Q d.radical a)).map (Q d.radical a).subtype ∧
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ≤ fixedCore d.radical a ∧
      ⁅fixedCore d.radical z,Q d.radical t⁆ ≤
        (frattini (Q d.radical z)).map (Q d.radical z).subtype ∧
      (frattini (Q d.radical z)).map (Q d.radical z).subtype ≤ fixedCore d.radical z :=
  ⟨fixedCore_displacement_le_frattini h d g hb path.start_color c,
    frattini_le_fixedCore h d g hb path.start_color,
    fixedCore_displacement_le_frattini h d g hb path.end_color c',
    frattini_le_fixedCore h d g hb path.end_color⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
