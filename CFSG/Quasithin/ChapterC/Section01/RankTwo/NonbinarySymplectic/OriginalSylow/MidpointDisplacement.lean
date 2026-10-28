module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalSylow.MidpointQuadratic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoDisplacementBounds
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalSylow.MidpointQuadratic
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoDisplacementBounds
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.CriticalFixedLayers
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoDisplacementBounds
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoActorBound

/-!
# Original Sylow fixed-core displacement and actor bounds

For the literal original Sylow marking, fixed-core quadraticity and the
large-movement critical image estimate give the full-cover displacement
bounds of MS93 (3.7)(2), printed p.873. The critical commutator retains the
complete fixed attachments. Its relative index in the fixed-core
displacement is at most q, the displacement has order at most q times the
attachment order, and the fixed-core image modulo the opposite core has
order at most 2q.

The common critical-pair and full-cover arguments are reused from the
original-star and generic cover modules. All cores, attachments and
markings belong to the original input.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
open DistanceTwoRecognition ChapterB.QuasisimpleSource MSCentralOrbit OriginalStar
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
include h hshort hinner

/-- In the large-movement branch the fixed-core displacement adds at most
q cosets to the actual critical commutator. The full cover kernel stays
inside that commutator throughout the quotient calculation. -/
theorem original_source_two_large_displacement_index
    (g : Geometry R) (hb : g.b R = 2)
    (hsy : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
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
  have hcrit := (OriginalSylow.original_large_movement_images h hshort hinner hsy g hb path hat hzt hlarge).2.2.1
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
      (OriginalSylow.original_fixedCore_quadratic h hshort hinner hsy g hb path hat hzt).le) bot_le
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
    (hsy : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
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
  have hindex := original_source_two_large_displacement_index h hshort hinner g hb hsy path hat hzt hlarge
  have hmul : Nat.card (W.subgroupOf C) * W.relIndex C = Nat.card C :=
    (W.subgroupOf C).card_mul_index
  change Nat.card C ≤ 2^n * Nat.card A
  rw [←hmul,mul_comm (2^n)]
  exact Nat.mul_le_mul hc hindex

/-- MS93 (3.7)(2), p.873: the actual image of D modulo the opposite full
core has order at most 2q. -/
theorem original_source_two_large_fixedCore_actor_index
    (g : Geometry R) (hb : g.b R = 2)
    (hsy : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
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
      (OriginalSylow.original_fixedCore_quadratic h hshort hinner hsy g hb path hat hzt).le) bot_le
  have hm := original_source_two_large_displacement_card h hshort hinner g hb hsy path hat hzt hlarge
  rw [original_fixedCore_displacement_eq_moving h hshort hinner g hb path hat hzt,
    commutator_comm (U R z)] at hm
  have hcards := (original_critical_paired_fixed_layers h hshort hinner path hb hat hzt
    ((OriginalSylow.original_large_movement_images h hshort hinner hsy g hb path hat hzt hlarge).2.2.1)).2.2.2.2
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

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
