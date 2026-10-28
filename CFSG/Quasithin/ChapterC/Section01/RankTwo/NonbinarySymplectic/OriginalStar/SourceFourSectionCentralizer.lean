module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourFullSaturation
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourEscape
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourSectionCentralizer

/-!
# Section centralizers for the original escaping hyperplane

At full attachment order, the original moving group inherits the covering
field. The opposite section centralizer equals the pointwise centralizer.
The proof removes the central midpoint supplement through the literal
original embedding before applying the field-linear calculation.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(4), printed p.875.
The original radical, quotient marking and complete fixed attachments are
retained. Internal imports reuse generic cover and subgroup calculations;
no saturation premise for a characteristic replacement is used.
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
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
variable (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
  (R.subgroupOf K).map (componentProjection h))
include h hshort hinner hnsyl

omit hshort hinner hnsyl in
private theorem full_plane_section_centralizer
    {a t : Vertex R}
    (cv : SaturatedDistanceTwo.RadicalPlaneCover R (originalMovedSection h) n a t)
    (hfull : Nat.card (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) :
      Subgroup (FreeAmalgam R))=2^n)
    (X B : Subgroup (FreeAmalgam R)) (hX : X ≤ Q R t) (hB : B ≤ Q R t)
    (hi : (centralizer (X : Set (FreeAmalgam R))).relIndex (U R a)=2^n)
    (hn : ¬ ⁅X,U R a⁆ ≤
      ⁅B,U R a ⊓ centralizer (X : Set (FreeAmalgam R))⁆)
    (u : FreeAmalgam R) (hu : u ∈ U R a) :
    (∀ x ∈ X, ⁅x,u⁆ ∈ ⁅B,U R a ⊓ centralizer (X : Set (FreeAmalgam R))⁆) ↔
      u ∈ centralizer (X : Set (FreeAmalgam R)) := by
  let p := MovedSection.coverProjection (originalMovedSection h) cv.equiv
  have hk : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map cv.embedding=
      U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) := by
    apply le_antisymm
    · rintro v ⟨w,hw,rfl⟩
      exact ⟨cv.range_eq ▸ ⟨w,rfl⟩,(cv.kernel _).mp hw⟩
    · rintro v ⟨hv,hc⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hv
      exact ⟨w,(cv.kernel _).mpr hc,rfl⟩
  have hFc : Nat.card cv.field.Carrier=2^n := cv.field.card_eq.trans (congrArg (2^·) cv.degree)
  have hc : Nat.card p.toLinearMap.ker=Nat.card cv.field.Carrier := by
    rw [←embedded_cover_kernel_card p cv.embedding cv.injective,hk,hfull,hFc]
  obtain ⟨j,hj,hr,hβ,hγ⟩ := full_cover_embedding p cv.cover hc
    cv.embedding cv.injective (U R a) X B cv.range_eq
    (cv.actor.comp (inclusion hX)) (cv.actor.comp (inclusion hB))
    (fun x w => cv.actor_conjugation (inclusion hX x) w)
    (fun b w => cv.actor_conjugation (inclusion hB b) w)
  have hi' : (centralizer (X : Set (FreeAmalgam R))).relIndex j.range=Nat.card cv.field.Carrier := by
    rwa [hr,hFc]
  have hh := embedded_section_centralizer action j hj X B _ _ hβ hγ hi'
    (by rwa [hr]) u (by rwa [hr])
  rwa [hr] at hh
/-- On the full opposite Z, centralizing the selected hyperplane modulo
its root movement is equivalent to centralizing that hyperplane pointwise.
The arbitrary endpoint markings and entire fixed attachment are retained. -/
theorem original_source_four_large_full_section_centralizer
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (P : Subgroup (FreeAmalgam R)) (hP : P ≤ Q R t)
    (hpoint : P=Q R t ⊓ centralizer
      (Z R z ⊓ centralizer (P : Set (FreeAmalgam R)) : Set (FreeAmalgam R)))
    (hi : (Z R z ⊓ centralizer (P : Set (FreeAmalgam R))).relIndex (Z R z)=2^n)
    (hescape : ¬ Z R a ⊓ centralizer
      (Z R z ⊓ centralizer (P : Set (FreeAmalgam R)) : Set (FreeAmalgam R)) ≤ Q R z)
    (hfull : Nat.card (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) :
      Subgroup (FreeAmalgam R))=2^n)
    (hMnot : ¬ ⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),Z R a⁆ ≤
      ⁅Z R z,P⁆)
    (u : FreeAmalgam R) (hu : u ∈ Z R a) :
    (∀ x ∈ Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),
      ⁅x,u⁆ ∈ ⁅Z R z,P⁆) ↔
      u ∈ centralizer (Z R z ⊓ centralizer (P : Set (FreeAmalgam R)) :
        Set (FreeAmalgam R)) := by
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  let X := Z R z ⊓ centralizer (P : Set (FreeAmalgam R))
  let Y₀ := U R a ⊓ centralizer (X : Set (FreeAmalgam R))
  let C := Z R t
  have geom := original_source_four_large_paired_geometry h hshort hinner hnsyl g hb path hat hzt hcritical
  let cv := Classical.choice geom.1
  have hzQ : Z R z ≤ Q R z :=
    (g.omega_bound z path.end_color (by rw [g.distance_constant z path.end_color]; change 0 < g.b R; omega)).trans (omegaCenter_le _)
  have hZT : Z R z ≤ Q R t := hzQ.trans (Q_le_adjacent_h R ht hzt)
  have hXT : X ≤ Q R t := inf_le_left.trans hZT
  have hCT : C ≤ centralizer (Q R t : Set (FreeAmalgam R)) :=
    midpoint_centralizes_radical path.end_color hzt
  have hCA : C ≤ Z R a := Sp4Four.edge_Z_le_endpoint R path.start_color hat
  let := g.Z_elementary (by omega : 0 < g.b R) a path.start_color
  let := finite_Z R a
  have hCU : C ≤ normalizer (U R a : Set (FreeAmalgam R)) :=
    (hCA.trans ((Z R a).le_centralizer.trans (centralizer_le (U_le_Z a)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCY : C ≤ normalizer (Y₀ : Set (FreeAmalgam R)) :=
    (hCA.trans ((Z R a).le_centralizer.trans (centralizer_le
      (inf_le_left.trans (U_le_Z a))))).trans (Subgroup.centralizer_le_normalizer _)
  have hY : Z R a ⊓ centralizer (X : Set (FreeAmalgam R))=Y₀ ⊔ C := by
    rw [original_Z_eq_moving_sup_edge h hshort hinner g hb path.start_color hat,
      sup_comm (U R a),inf_centralizer_sup_of_centralizing C (U R a) X
        hCU (hCT.trans (centralizer_le hXT)),sup_comm]
  have hM : ⁅X,Z R a⁆=⁅X,U R a⁆ := by
    rw [original_Z_eq_moving_sup_edge h hshort hinner g hb path.start_color hat]
    exact movement_central_supplement (U R a) C (Q R t) X hCU hCT hXT
  have hH : ⁅Z R z,P⁆=⁅Z R z,Y₀⁆ := by
    rw [(original_source_four_large_escaping_hyperplane h hshort hinner hnsyl g hb path hat hzt
      hcritical P hP hpoint hi hescape).2.2.2,hY]
    exact movement_central_supplement Y₀ C (Q R t) (Z R z) hCY hCT hZT
  have hYindex : Y₀.relIndex (U R a)=2^n := by
    rw [inf_relIndex_left]
    rw [←central_supplement_fixed_index (U R a) C (Z R a) X
      (U_le_Z a) hCA (original_Z_eq_moving_sup_edge h hshort hinner g hb path.start_color hat)
      (hCT.trans (centralizer_le hXT))]
    rw [←inf_relIndex_left]
    exact (original_source_four_large_escaping_hyperplane h hshort hinner hnsyl g hb path hat hzt
      hcritical P hP hpoint hi hescape).1
  have hu' : u ∈ U R a ⊔ C := by
    rwa [←original_Z_eq_moving_sup_edge h hshort hinner g hb path.start_color hat]
  rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hCU] at hu'
  obtain ⟨v,hv,w,hw,rfl⟩ := hu'
  have hval (x : FreeAmalgam R) (hx : x ∈ X) : ⁅x,v*w⁆=⁅x,v⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_eq_one_iff_commute.mpr (hCT hw x (hXT hx))]
    simp only [mul_one,mul_inv_cancel_right]
  have hfix : v*w ∈ centralizer (X : Set (FreeAmalgam R)) ↔
      v ∈ centralizer (X : Set (FreeAmalgam R)) := by
    constructor
    · intro hc x hx
      apply commutatorElement_eq_one_iff_commute.mp
      rw [←hval x hx,commutatorElement_eq_one_iff_commute.mpr (hc x hx)]
    · intro hc x hx
      apply commutatorElement_eq_one_iff_commute.mp
      rw [hval x hx,commutatorElement_eq_one_iff_commute.mpr (hc x hx)]
  change (∀ x ∈ X, ⁅x,v*w⁆ ∈ ⁅Z R z,P⁆) ↔
    v*w ∈ centralizer (X : Set (FreeAmalgam R))
  rw [hfix]
  have hh := full_plane_section_centralizer h cv hfull X (Z R z) hXT hZT
    (by rwa [inf_relIndex_left] at hYindex) (by rwa [←hM,←hH]) v hv
  rw [←hH] at hh
  exact (forall₂_congr fun x hx => by rw [hval x hx]).trans hh



end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
