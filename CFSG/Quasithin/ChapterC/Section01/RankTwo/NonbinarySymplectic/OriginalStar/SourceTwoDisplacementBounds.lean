module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoActorBound
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.CriticalFixedLayers
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoDisplacementBounds
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoActorBound

/-!
# Original-star displacement and actor bounds

Let T be the original source star, Q and Q′ its complete endpoint cores,
D = C_Q(L), and A and A′ the complete fixed attachments of U and U′.
In the large-movement branch of MS93 (3.7)(2), the critical image has
order q. The actual critical long root preserves no quadratic refinement,
so its full-cover commutator contains the whole fixed attachment with
index q. Applying this in both orientations gives
A A′ ≤ W = [Z,Z′] = [U,U′] and |A| = |A′|.

The preceding original-star quadraticity result makes the natural images
of [Z′,D] and W span an isotropic space of dimension at most two. Keeping
the entire cover kernel gives [ [Z′,D] : W ∩ [Z′,D] ] ≤ q. As the
intersection lies in A, this proves |[Z′,D]| ≤ q|A′|. The full cover then
bounds the actual opposite-core image |DQ′/Q′| by 2q.

The final theorem applies both bounds to the selected original star with
its literal quotient marking, restricted original odd-index witness and
own distance-two geometry. Shortness and innerness are discharged from
that construction. The private generic cover arguments are reused from
the saturated branch; no minimum-radical saturation is assumed here.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.7)(2), printed p.873, from the paragraph following
[Z′,D,D] = 1 through |DQ′/Q′| ≤ 2q. The subsequent point-radical and q²
fixed-core comparison on pp.873--874, minimum marked preservation and
saturation, original Sylow branch, field restriction and block assembly
remain obligations of the original distance-two argument.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open DistanceTwoRecognition ChapterB.QuasisimpleSource MSCentralOrbit
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
include h hshort hinner

/-- The common edge center contributes no critical displacement. -/
theorem original_critical_displacement_eq_moving
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    ⁅Z R a,Z R z⁆ = ⁅U R a,Z R z⁆ := by
  let := g.Z_elementary (by omega : 0 < g.b R) z path.end_color
  have hc : Z R t ≤ centralizer (Z R z : Set (FreeAmalgam R)) :=
    (Sp4Four.edge_Z_le_endpoint R path.end_color hzt).trans
      (Z R z).le_centralizer
  apply le_antisymm ?_ (commutator_mono (U_le_Z a) le_rfl)
  rw [commutator_comm (Z R a),commutator_comm (U R a)]
  apply commutator_le_moving_of_inner_mod_centralizer (Z R z)
    (U R a) (Z R a)
    (((U_le_Z a).trans (Z_le_stabilizer_of_dist_le a
      (g.exists_critical a path.start_color) path.critical.1.le)).trans (Z_normalized R z))
  rw [original_Z_eq_moving_sup_edge h hshort hinner g hb path.start_color hat]
  exact sup_le_sup_left hc _

/-- Both full natural covers supply the common critical commutator. -/
theorem original_critical_displacement_eq_paired_moving
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    ⁅Z R a,Z R z⁆ = ⁅U R a,U R z⁆ := by
  have hUZ : U R z ≤ normalizer (U R a : Set (FreeAmalgam R)) :=
    (U_le_Z z).trans
      (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_reverse_actor_normalizes_moving path)
  let := g.Z_elementary (by omega : 0 < g.b R) a path.start_color
  have hcent : Z R t ≤ centralizer (U R a : Set (FreeAmalgam R)) :=
    (Sp4Four.edge_Z_le_endpoint R path.start_color hat).trans
      ((Z R a).le_centralizer.trans (centralizer_le (U_le_Z a)))
  have hZa : Z R z ≤ U R z ⊔ centralizer
      (U R a : Set (FreeAmalgam R)) := by
    rw [original_Z_eq_moving_sup_edge h hshort hinner g hb path.end_color hzt]
    exact sup_le_sup_left hcent _
  rw [original_critical_displacement_eq_moving h hshort hinner path hb hat hzt]
  exact le_antisymm (commutator_le_moving_of_inner_mod_centralizer
    (U R a) (U R z) (Z R z) hUZ hZa)
    (commutator_mono le_rfl (U_le_Z z))

/-- The common critical displacement contains the entire fixed attachment;
its quotient by that attachment has order q at the original field degree. -/
theorem original_critical_fixed_layer_index
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n) :
    let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
    A ≤ ⁅Z R a,Z R z⁆ ∧
      A.relIndex ⁅Z R a,Z R z⁆ = 2^n := by
  let := h.component_normal
  let q := QuotientGroup.mk' (pCore 2 H)
  let C₀ := K.map q
  let : C₀.Normal := h.component_image_structure.2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)) C₀
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex path.start_color
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  obtain ⟨haq,hzq⟩ := h.original_small_critical_indices_eq_field path (by omega) (by
    rw [hcritical,h.field_card]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)
  rw [h.field_card] at haq hzq
  have hZA : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  let δ := κ.comp (inclusion hZA)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZA κ hκQ).trans (hzq.trans hFc.symm)
  have hδ : ∀ x : Z R z, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam R)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam R)⁻¹ :=
    fun x v => hconj (inclusion hZA x) v
  obtain ⟨β,hβcard,hβmark,hβ,hβdim,hβquad⟩ := inner_root_actor_of_field_index rev (by omega)
    (MSCentralOrbit.C_eq_Q R h.radical.isPGroup
      h.radical.twoCore_le h.omegaOrbit_centralizer z path.end_color)
    h.nonbinary hFc s e he h.component_image_structure.2.2.2.2
    j hj hjr δ hδ hδcard (haq.trans hFc.symm)
  have hcard : 2 < Nat.card E.Carrier := by
    rw [hFc]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hh := SaturatedDistanceTwo.embedded_root_displacement_index (U R a) (Z R z)
    (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_reverse_actor_normalizes_moving path)
    (MovedSection.coverAction s e) (MovedSection.coverProjection s e) he j hj hjr β hβ
    hcard hβcard hβdim hβquad
  have hk : (MovedSection.coverProjection s e).toLinearMap.ker.toAddSubgroup.toSubgroup.map j =
      U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) := by
    apply le_antisymm
    · rintro x ⟨v,hv,rfl⟩
      exact ⟨hjr ▸ ⟨v,rfl⟩,(hker v.toAdd).mp hv⟩
    · rintro x ⟨hx,hc⟩
      obtain ⟨v,rfl⟩ := hjr.symm ▸ hx
      exact ⟨v,(hker v.toAdd).mpr hc,rfl⟩
  dsimp only at hh
  rw [hk,commutator_comm (Z R z),
    ←original_critical_displacement_eq_moving h hshort hinner path hb hat hzt,hFc] at hh
  exact hh


/-- Both full fixed attachments lie in the common elementary displacement,
and they have the same order. Equality or vanishing is not assumed. -/
theorem original_critical_paired_fixed_layers
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n) :
    let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
    let A' := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
    let W := ⁅Z R a,Z R z⁆
    W = ⁅U R a,U R z⁆ ∧
      A ⊔ A' ≤ W ∧ W ≤ U R a ⊓ U R z ∧
      Nat.card W = 2^n * Nat.card A ∧ Nat.card A = Nat.card A' := by
  let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
  let A' := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
  let W := ⁅Z R a,Z R z⁆
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  have hother := (h.original_small_critical_indices_eq_field path (by omega) (by
    rw [hcritical,h.field_card]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)).2
  rw [h.field_card] at hother
  have ha := original_critical_fixed_layer_index h hshort hinner path hb hat hzt hcritical
  have hz := original_critical_fixed_layer_index h hshort hinner rev hb hzt hat hother
  rw [commutator_comm (Z R z)] at hz
  have hWU : W ≤ U R a := by
    rw [show W = ⁅Z R a,Z R z⁆ from rfl,
      original_critical_displacement_eq_moving h hshort hinner path hb hat hzt]
    exact le_normalizer_iff_commutator_le_left.mp
      (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_reverse_actor_normalizes_moving path)
  have hWU' : W ≤ U R z := by
    rw [show W = ⁅Z R a,Z R z⁆ from rfl,commutator_comm,
      original_critical_displacement_eq_moving h hshort hinner rev hb hzt hat]
    exact le_normalizer_iff_commutator_le_left.mp
      (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_actor_normalizes_moving path)
  let := finite_Z R a
  let : Finite W := Finite.of_injective (inclusion (hWU.trans (U_le_Z a)))
    (inclusion_injective _)
  have hcard : Nat.card A * 2^n = Nat.card W := by
    have hi := (A.subgroupOf W).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe ha.1).toEquiv] at hi
    exact ha.2 ▸ hi
  have hcard' : Nat.card A' * 2^n = Nat.card W := by
    have hi := (A'.subgroupOf W).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hz.1).toEquiv] at hi
    exact hz.2 ▸ hi
  exact ⟨original_critical_displacement_eq_paired_moving h hshort hinner path hb hat hzt,
    sup_le ha.1 hz.1,le_inf hWU hWU',by rw [←hcard,Nat.mul_comm],
    Nat.eq_of_mul_eq_mul_right (by positivity) (hcard.trans hcard'.symm)⟩

/-- The actual full fixed-core displacement meets the critical commutator
only inside the original endpoint's complete fixed attachment. -/
theorem original_critical_commutator_inf_fixedCore_displacement
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    ⁅Z R a,Z R z⁆ ⊓ ⁅Z R z,fixedCore R a⁆ ≤
      U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hRU : ⁅Z R a,Z R z⁆ ≤ U R a := by
    rw [original_critical_displacement_eq_moving h hshort hinner path hb hat hzt]
    exact le_normalizer_iff_commutator_le_left.mp
      (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_reverse_actor_normalizes_moving path)
  have hZt : Z R z ≤ Q R t :=
    Z_le_Q_of_dist_lt R z (g.exists_critical z path.end_color) (by
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
        g.distance_constant z path.end_color]
      change 1 < g.b R
      omega)
  have hCD : ⁅Z R z,fixedCore R a⁆ ≤ fixedCore R a :=
    le_normalizer_iff_commutator_le_right.mp (hZt.trans (original_fixedCore_normalized hat))
  exact le_inf (inf_le_left.trans hRU) (inf_le_right.trans (hCD.trans inf_le_right))

/-- The full edge center is fixed by D, so all of [Z′,D] comes from U′. -/
theorem original_fixedCore_displacement_eq_moving
    (g : Geometry R) (hb : g.b R = 2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    ⁅Z R z,fixedCore R a⁆ = ⁅U R z,fixedCore R a⁆ := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hAT : fixedCore R a ≤ Q R t := inf_le_left.trans (Q_le_adjacent_h R ht hat)
  have hc : Z R t ≤ centralizer (fixedCore R a : Set (FreeAmalgam R)) := by
    have he : Z R t = omegaCenter (Q R t) := by simp [Z,ht,edgeOmega]
    rw [he]
    exact fun x hx y hy => (mem_omegaCenter_iff.mp hx).2.2 y (hAT hy)
  have hUzT : U R z ≤ Q R t :=
    ((original_component_core_intersection h hshort path.end_color).ge.trans inf_le_right).trans
      (Q_le_adjacent_h R ht hzt)
  apply le_antisymm ?_ (commutator_mono (U_le_Z z) le_rfl)
  rw [commutator_comm (Z R z),commutator_comm (U R z)]
  apply commutator_le_moving_of_inner_mod_centralizer (fixedCore R a)
    (U R z) (Z R z) (hUzT.trans (original_fixedCore_normalized hat))
  rw [original_Z_eq_moving_sup_edge h hshort hinner g hb path.end_color hzt]
  exact sup_le_sup_left hc _

/-- In the large-movement branch the fixed-core displacement adds at most
q cosets to the actual critical commutator. The full cover kernel stays
inside that commutator throughout the quotient calculation. -/
theorem original_source_two_large_displacement_index
    (g : Geometry R) (hb : g.b R = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z)) :
    (⁅Z R a,Z R z⁆).relIndex ⁅Z R z,fixedCore R a⁆ ≤ 2^n := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  let := h.component_normal
  let := finite_Z R z
  let : Finite (U R z) := Finite.of_injective
    (inclusion (U_le_Z z)) (inclusion_injective _)
  let := g.Z_elementary (by omega : 0 < g.b R) z path.end_color
  let : IsElementaryAbelian 2 (U R z) :=
    IsElementaryAbelian.of_injective (inclusion (U_le_Z z)) (inclusion_injective _)
  let q := QuotientGroup.mk' (pCore 2 H)
  let C₀ := K.map q
  let : C₀.Normal := h.component_image_structure.2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)) C₀
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex path.end_color
  have hCtop : C₀ = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hh := congrArg (fun A : Subgroup H => A.map q)
      hinner
    rw [Subgroup.map_sup,show (pCore 2 H).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (C₀) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  have haction (x : stabilizer R z) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (γ x) w)) =
        x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x w
  have hAS : fixedCore R a ≤ stabilizer R z :=
    (inf_le_left.trans (Q_le_adjacent_h R ht hat)).trans (show Q R t ≤ stabilizer R z from fun _ hx => hx.2 _ (adjacent_symm R hzt))
  have hBS : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  let βA := γ.comp (inclusion hAS)
  let βB := γ.comp (inclusion hBS)
  have hk : (MovedSection.coverProjection s e).toLinearMap.ker.toAddSubgroup.toSubgroup.map j =
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
    apply le_antisymm
    · rintro x ⟨v,hv,rfl⟩
      exact ⟨hjr ▸ ⟨v,rfl⟩,(hker v.toAdd).mp hv⟩
    · rintro x ⟨hx,hc⟩
      obtain ⟨v,rfl⟩ := hjr.symm ▸ hx
      exact ⟨v,(hker v.toAdd).mpr hc,rfl⟩
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  have hcrit := (original_large_movement_images h hshort hinner hnsyl g hb path hat hzt hlarge).2.2.1
  have hother := (h.original_small_critical_indices_eq_field path (by omega) (by
    rw [hcrit,h.field_card]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)).2
  rw [h.field_card] at hother
  have hf := original_critical_fixed_layer_index h hshort hinner rev hb hzt hat hother
  have hR : ⁅Z R a,Z R z⁆ = ⁅Z R a,U R z⁆ := by
    rw [commutator_comm (Z R a),original_critical_displacement_eq_moving h hshort hinner rev hb hzt hat,
      commutator_comm]
  rw [commutator_comm (Z R z),hR] at hf
  have haa : ⁅⁅fixedCore R a,U R z⁆,fixedCore R a⁆=⊥ := by
    rw [commutator_comm (fixedCore R a)]
    exact le_antisymm ((commutator_mono (commutator_mono (U_le_Z z) le_rfl) le_rfl).trans
      (original_fixedCore_quadratic h hshort hinner hnsyl g hb path hat hzt).le) bot_le
  have hRZa : ⁅Z R a,U R z⁆ ≤ Z R a := by
    rw [←hR,original_critical_displacement_eq_paired_moving h hshort hinner path hb hat hzt]
    exact (le_normalizer_iff_commutator_le_left.mp ((U_le_Z z).trans
      (Sp4Four.SourceComparison.critical_reverse_actor_normalizes_moving path))).trans (U_le_Z a)
  let := g.Z_elementary (by omega : 0 < g.b R) a path.start_color
  have hbb : ⁅⁅Z R a,U R z⁆,Z R a⁆=⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hRZa.trans (Z R a).le_centralizer)
  have hUD : ⁅fixedCore R a,U R z⁆ ≤ fixedCore R a :=
    le_normalizer_iff_commutator_le_left.mp
      (((U_le_Z z).trans (Z_le_stabilizer_of_dist_le z
        (g.exists_critical z path.end_color) (by
          rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
            g.distance_constant z path.end_color]))).trans ((le_inf (Q_normalized R a)
        ((original_residual_normalized a).trans (normalizer_le_normalizer_centralizer _))).trans
          inf_normalizer_le_normalizer_inf))
  have hab : ⁅⁅fixedCore R a,U R z⁆,Z R a⁆=⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply hUD.trans
    apply (show fixedCore R a ≤ Q R a from inf_le_left).trans
    rw [←commutator_eq_bot_iff_le_centralizer,commutator_comm]
    exact Z_centralizes_Q R a path.start_color
  have hh := cover_quadratic_sup_index (MovedSection.coverAction s e)
    (MovedSection.coverProjection s e) he (U R z)
    (fixedCore R a) (Z R a) j hj hjr βA βB
    (fun x => haction (inclusion hAS x)) (fun x => haction (inclusion hBS x))
    (hAS.trans (U_normalized z)) (hBS.trans (U_normalized z)) haa hbb hab
    (hk.symm ▸ hf.1) (by rw [hk]; simpa only [E.card_eq,hE] using hf.2)
  rw [original_fixedCore_displacement_eq_moving h hshort hinner g hb path hat hzt,hR,
    commutator_comm (U R z)]
  simpa only [E.card_eq,hE] using hh

/-- The next source estimate in (3.7)(2), printed p.873: the full
fixed-core displacement has order at most q times the first fixed
attachment. The attachment is retained as an actual subgroup. -/
theorem original_source_two_large_displacement_card
    (g : Geometry R) (hb : g.b R = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z)) :
    Nat.card (⁅Z R z,fixedCore R a⁆ : Subgroup (FreeAmalgam R)) ≤
      2^n * Nat.card (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) : Subgroup (FreeAmalgam R)) := by
  let W := ⁅Z R a,Z R z⁆
  let C := ⁅Z R z,fixedCore R a⁆
  let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
  let := finite_Z R a
  let : Finite A := Finite.of_injective (inclusion (inf_le_left.trans (U_le_Z a))) (inclusion_injective _)
  have hi := original_critical_commutator_inf_fixedCore_displacement h hshort hinner path hb hat hzt
  let f : W.subgroupOf C → A := fun x => ⟨x.val.val,hi ⟨x.property,x.val.property⟩⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun x : A => x.val) he))
  have hc := Nat.card_le_card_of_injective f hf
  have hindex := original_source_two_large_displacement_index h hshort hinner g hb hnsyl path hat hzt hlarge
  have hmul : Nat.card (W.subgroupOf C) * W.relIndex C = Nat.card C :=
    (W.subgroupOf C).card_mul_index
  change Nat.card C ≤ 2^n * Nat.card A
  rw [←hmul,mul_comm (2^n)]
  exact Nat.mul_le_mul hc hindex

/-- MS93 (3.7)(2), p.873: the actual image of D modulo the opposite full
core has order at most 2q. -/
theorem original_source_two_large_fixedCore_actor_index
    (g : Geometry R) (hb : g.b R = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z)) :
    (Q R z).relIndex (fixedCore R a) ≤ 2 * 2^n := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  let := h.component_normal
  let := finite_Z R z
  let : Finite (U R z) := Finite.of_injective
    (inclusion (U_le_Z z)) (inclusion_injective _)
  let q := QuotientGroup.mk' (pCore 2 H)
  let C₀ := K.map q
  let : C₀.Normal := h.component_image_structure.2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)) C₀
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex path.end_color
  have hCtop : C₀ = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hh := congrArg (fun A : Subgroup H => A.map q)
      hinner
    rw [Subgroup.map_sup,show (pCore 2 H).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (C₀) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  have haction (x : stabilizer R z) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (γ x) w)) =
        x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x w
  have hAS : fixedCore R a ≤ stabilizer R z :=
    (inf_le_left.trans (Q_le_adjacent_h R ht hat)).trans (show Q R t ≤ stabilizer R z from fun _ hx => hx.2 _ (adjacent_symm R hzt))
  let β := γ.comp (inclusion hAS)
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  have hk : (MovedSection.coverProjection s e).toLinearMap.ker.toAddSubgroup.toSubgroup.map j =
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
    apply le_antisymm
    · rintro x ⟨v,hv,rfl⟩
      exact ⟨hjr ▸ ⟨v,rfl⟩,(hker v.toAdd).mp hv⟩
    · rintro x ⟨hx,hc⟩
      obtain ⟨v,rfl⟩ := hjr.symm ▸ hx
      exact ⟨v,(hker v.toAdd).mpr hc,rfl⟩
  have hquad : ⁅⁅U R z,fixedCore R a⁆,fixedCore R a⁆=⊥ :=
    le_antisymm ((commutator_mono (commutator_mono (U_le_Z z) le_rfl) le_rfl).trans
      (original_fixedCore_quadratic h hshort hinner hnsyl g hb path hat hzt).le) bot_le
  have hm := original_source_two_large_displacement_card h hshort hinner g hb hnsyl path hat hzt hlarge
  rw [original_fixedCore_displacement_eq_moving h hshort hinner g hb path hat hzt,
    commutator_comm (U R z)] at hm
  have hcards := (original_critical_paired_fixed_layers h hshort hinner path hb hat hzt
    ((original_large_movement_images h hshort hinner hnsyl g hb path hat hzt hlarge).2.2.1)).2.2.2.2
  rw [hcards] at hm
  have hbound := cover_actor_bound_of_small_displacement (MovedSection.coverAction s e)
    (MovedSection.coverProjection s e) he (U R z) (fixedCore R a)
    j hj hjr β (fun x => haction (inclusion hAS x)) (hAS.trans (U_normalized z)) hquad
    (by simpa only [hk,E.card_eq,hE] using hm)
  have hαker : α.ker = (Q R z).subgroupOf (fixedCore R a) := by
    have hkκ : κ.ker = (Q R z).subgroupOf (stabilizer R z) := by
      rw [←hκQ,subgroupOf_map_subtype_eq]
    dsimp only [α,β,γ]
    rw [MonoidHom.ker_comp_of_injective _ _ (commutator (Sp E.Carrier)).subtype_injective,
      MonoidHom.comp_assoc,MonoidHom.ker_comp_of_injective _ _ e.groupEquiv.injective,
      ←MonoidHom.comap_ker,MonoidHom.ker_codRestrict,hkκ,comap_inclusion_subgroupOf]
  have hi : (Q R z).relIndex (fixedCore R a)=Nat.card α.range := by
    rw [relIndex,←hαker,index_ker]
  rw [hi]
  simpa only [E.card_eq,hE] using hbound

omit hshort hinner in
/-- MS93 (3.7)(2), p.873, applied to the original marked source star.
Both fixed attachments and the actual quotient marking are retained. -/
theorem exists_source_star_fixedCore_displacement_bounds
    (d : CharacteristicReduction K R) (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h)) :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R,
      Y.map (embedS R) = componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      d.subgroup ≤ starCentralizer R Y ∧
      (let T := (starCentralizer R Y).map R.subtype
       let M := K ⊔ T
       let S := T.subgroupOf M
       ∃ hs : Input (K.subgroupOf M) S n F, ∃ gs : Geometry S,
         hs.quotientEquiv = (subgroupOfCoreQuotientEquiv le_sup_left).trans h.quotientEquiv ∧
         S = R.subgroupOf M ∧
         (normalizer (S : Set M)).pCoreIn 2 = S ∧
         ((T.subgroupOf K).map (componentProjection h)) =
           (R.subgroupOf K).map (componentProjection h) ∧
         gs.b S = 2 ∧
         ∀ (a z t : Vertex S) (_path : CriticalPath S gs a z),
           Adjacent S a t → Adjacent S z t →
           (2^n)^2 < (centralizer (Q S a : Set (FreeAmalgam S))).relIndex (U S z) →
           (let A := U S a ⊓ centralizer (Ltilde S a : Set (FreeAmalgam S))
            let A' := U S z ⊓ centralizer (Ltilde S z : Set (FreeAmalgam S))
            let W := ⁅Z S a,Z S z⁆
            A ⊔ A' ≤ W ∧ Nat.card A = Nat.card A' ∧
              Nat.card (⁅Z S z,fixedCore S a⁆ : Subgroup (FreeAmalgam S)) ≤ 2^n * Nat.card A' ∧
              (Q S z).relIndex (fixedCore S a) ≤ 2 * 2^n)) := by
  obtain ⟨P,Y,hY,hn,hmin,hs,hquot,hrest,hsat,hinner,hmark,hsyl,gs,hgs⟩ :=
    exists_source_star_intrinsic_distance_two h d g hb
  have hshort := (short_and_natural_of_distance_two h d g hb).1
  have hstarshort : IsShort (K.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype)) :=
    hshort.of_mulEquiv (subgroupOfEquivOfLe le_sup_left).symm
  have hstar_nsyl : ¬ ∃ S' : Sylow 2 (Sp F), (S' : Subgroup (Sp F)) =
      ((((starCentralizer R Y).map R.subtype).subgroupOf
        (K ⊔ (starCentralizer R Y).map R.subtype)).subgroupOf
          (K.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype))).map (componentProjection hs) := by
    intro he
    exact hnsyl ((original_sylow_iff_marked_sylow h).mp
      (hsyl.mp ((original_sylow_iff_marked_sylow hs).mpr he)))
  refine ⟨P,Y,hY,hn,hmin,hs,gs,hquot,hrest,hsat,hmark,hgs,?_⟩
  intro a z t path hat hzt hlarge
  have hl := original_critical_paired_fixed_layers hs hstarshort hinner path hgs hat hzt
    ((original_large_movement_images hs hstarshort hinner hstar_nsyl gs hgs path hat hzt hlarge).2.2.1)
  refine ⟨hl.2.1,hl.2.2.2.2,?_,?_⟩
  · rw [←hl.2.2.2.2]
    exact original_source_two_large_displacement_card hs hstarshort hinner gs hgs hstar_nsyl path hat hzt hlarge
  · exact original_source_two_large_fixedCore_actor_index hs hstarshort hinner gs hgs hstar_nsyl path hat hzt hlarge


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
