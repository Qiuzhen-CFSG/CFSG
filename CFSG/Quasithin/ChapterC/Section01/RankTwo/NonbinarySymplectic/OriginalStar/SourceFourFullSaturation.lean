module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourFullIntersection
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourEscape
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourFullSaturation

/-!
# The second-field obstruction for the original hyperplane

At full attachment order, the original moving group is the universal
orthogonal cover. Vectors whose individual displacements lie in the
opposite root movement form a field subspace. A nontrivially moving vector
in the opposite hyperplane fills its one-dimensional quotient, forcing
containment of the whole hyperplane movement. Since the two movements are
distinct and have equal order, such a vector must have a value outside the
opposite movement. Both original field actions and full attachments remain.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(4), printed p.875,
the second-field argument in the escaping-centralizer subcase. This is
field-span saturation, not saturation of the characteristic replacement.
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
private theorem full_plane_fixed_hyperplane_saturation
    {a t : Vertex R}
    (cv : SaturatedDistanceTwo.RadicalPlaneCover R (originalMovedSection h) n a t)
    (hfull : Nat.card (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) :
      Subgroup (FreeAmalgam R))=2^n)
    (X B : Subgroup (FreeAmalgam R)) (hX : X ≤ Q R t) (hB : B ≤ Q R t)
    (hi : (centralizer (Q R t : Set (FreeAmalgam R))).relIndex
      (U R a ⊓ centralizer (X : Set (FreeAmalgam R)))=2^n)
    (y : FreeAmalgam R) (hy : y ∈ U R a ⊓ centralizer (X : Set (FreeAmalgam R)))
    (hyn : ∃ b ∈ B, ⁅b,y⁆ ≠ 1)
    (hym : ∀ b ∈ B, ⁅b,y⁆ ∈ ⁅X,U R a⁆) :
    ⁅B,U R a ⊓ centralizer (X : Set (FreeAmalgam R))⁆ ≤ ⁅X,U R a⁆ := by
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
  obtain ⟨j,hj,hr,hact,_⟩ := full_cover_embedding p cv.cover hc
    cv.embedding cv.injective (U R a) (Q R t) (Q R t) cv.range_eq
    cv.actor cv.actor cv.actor_conjugation cv.actor_conjugation
  have hi' : (centralizer (Q R t : Set (FreeAmalgam R))).relIndex
      (j.range ⊓ centralizer (X : Set (FreeAmalgam R)))=Nat.card cv.field.Carrier := by
    rwa [hr,hFc]
  have hh := embedded_fixed_hyperplane_saturation action j hj (Q R t) X B hX hB
    cv.actor hact hi' y (by rwa [hr]) hyn (by rwa [hr])
  rwa [hr] at hh

/-- A nontrivially moving element of the escaping opposite hyperplane
spans that hyperplane modulo its full radical fixed layer. Thus if all its
individual displacements lie in the opposite root movement, the whole
hyperplane movement lies there. This uses the original full cover and field. -/
theorem original_source_four_large_full_hyperplane_saturation
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
    (y : FreeAmalgam R)
    (hy : y ∈ Z R a ⊓ centralizer
      (Z R z ⊓ centralizer (P : Set (FreeAmalgam R)) : Set (FreeAmalgam R)))
    (hyn : ∃ b ∈ Z R z, ⁅b,y⁆ ≠ 1)
    (hym : ∀ b ∈ Z R z, ⁅b,y⁆ ∈
      ⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),Z R a⁆) :
    ⁅Z R z,P⁆ ≤
      ⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),Z R a⁆ := by
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
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  have hreverse : (2^n)^2 ≤ (Q R a).relIndex (Z R z) := by
    rw [(original_source_four_large_midpoint_kernels h hshort hinner hnsyl g hb path hat hzt hcritical).2.2.2]
  let D := U R a ⊓ centralizer (Q R t : Set (FreeAmalgam R))
  have hDY : D ≤ Y₀ := inf_le_inf_left _ (centralizer_le hXT)
  have hDindex : D.relIndex (U R a)=(2^n)^2 := by
    rw [inf_relIndex_left]
    exact (original_source_four_large_plane_cover h hshort hinner hnsyl g hb rev hzt hat hreverse).2.2.1
  have hindex : (centralizer (Q R t : Set (FreeAmalgam R))).relIndex Y₀=2^n := by
    have hh := relIndex_mul_relIndex D Y₀ (U R a) hDY inf_le_left
    rw [hYindex,hDindex,pow_two] at hh
    have he : D.relIndex Y₀=2^n := Nat.eq_of_mul_eq_mul_right (by positivity) hh
    have hDY' : Y₀ ⊓ centralizer (Q R t : Set (FreeAmalgam R))=D := by
      ext x
      exact ⟨fun hx => ⟨hx.1.1,hx.2⟩,fun hx => ⟨hDY hx,hx.2⟩⟩
    rwa [←inf_relIndex_left,hDY']
  change y ∈ Z R a ⊓ centralizer (X : Set (FreeAmalgam R)) at hy
  rw [hY,←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hCY] at hy
  obtain ⟨u,hu,v,hv,rfl⟩ := hy
  have hval (b : FreeAmalgam R) (hbZ : b ∈ Z R z) : ⁅b,u*v⁆=⁅b,u⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_eq_one_iff_commute.mpr (hCT hv b (hZT hbZ))]
    simp only [mul_one,mul_inv_cancel_right]
  have hun : ∃ b ∈ Z R z, ⁅b,u⁆ ≠ 1 := by
    obtain ⟨b,hbZ,hn⟩ := hyn
    exact ⟨b,hbZ,by rwa [←hval b hbZ]⟩
  have hum : ∀ b ∈ Z R z, ⁅b,u⁆ ∈ ⁅X,U R a⁆ := by
    intro b hbZ
    rw [←hM,←hval b hbZ]
    exact hym b hbZ
  change ⁅Z R z,P⁆ ≤ ⁅X,Z R a⁆
  rw [hH,hM]
  exact full_plane_fixed_hyperplane_saturation h cv hfull X (Z R z) hXT hZT
    hindex u hu hun hum

/-- When the two movements of order q squared are distinct, every nontrivially
moving element of the opposite hyperplane has an individual displacement
outside the root movement. This is the second-field obstruction on p.875. -/
theorem original_source_four_large_full_hyperplane_value_escape
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
    (hHcard : Nat.card (⁅Z R z,P⁆ : Subgroup (FreeAmalgam R))=(2^n)^2)
    (hMnot : ¬ ⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),Z R a⁆ ≤
      ⁅Z R z,P⁆)
    (y : FreeAmalgam R)
    (hy : y ∈ Z R a ⊓ centralizer
      (Z R z ⊓ centralizer (P : Set (FreeAmalgam R)) : Set (FreeAmalgam R)))
    (hyn : ∃ b ∈ Z R z, ⁅b,y⁆ ≠ 1) :
    ∃ b ∈ Z R z, ⁅b,y⁆ ∉
      ⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),Z R a⁆ := by
  classical
  by_contra hn
  push Not at hn
  have hle := original_source_four_large_full_hyperplane_saturation h hshort hinner hnsyl g hb path hat hzt
    hcritical P hP hpoint hi hescape hfull y hy hyn hn
  let M := ⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),Z R a⁆
  have hMcard : Nat.card M=(2^n)^2 := by
    have hh := (original_source_four_large_escaping_movement h hshort hinner hnsyl g hb path hat hzt
      hcritical P hP hpoint hi hescape).2.2
    simpa only [hfull,pow_two] using hh
  let : Finite M := Nat.finite_of_card_ne_zero (by rw [hMcard]; positivity)
  have he : ⁅Z R z,P⁆=M := Subgroup.eq_of_le_of_card_ge hle (by rw [hHcard,hMcard])
  exact hMnot he.ge

/-- The actual hyperplane of source (4) has the second-field value obstruction:
in the unequal-attachment escape branch, no nontrivially moving element of its
opposite centralizer has all its values in the movement intersection. The
full attachments, section centralizer and original marking are retained. -/
theorem original_source_four_large_unequal_value_escape
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (hne : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) ≠
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))) :
    ∃ P B : Subgroup (FreeAmalgam R),
      let X := Z R z ⊓ centralizer (P : Set (FreeAmalgam R))
      let H₀ := ⁅Z R z,P⁆
      let A₀ := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
      let A₁ := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
      Q R z ≤ P ∧ P ≤ Q R t ∧ B ≤ Q R t ∧
      P=Q R t ⊓ centralizer (X : Set (FreeAmalgam R)) ∧
      X.relIndex (Z R z)=2^n ∧
      Z R t ≤ X ∧ ⁅Z R a,Z R z⁆ ≤ X ∧
      (∀ b : FreeAmalgam R, b ∈ B ↔ b ∈ Q R t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam R))=2^n ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z R a,Z R z⁆ ∧
      (¬ Z R a ⊓ centralizer (X : Set (FreeAmalgam R)) ≤ Q R z →
        ¬ ⁅X,Z R a⁆ ≤ H₀ ∧
        Nat.card A₁=2^n ∧ Nat.card A₀=2^n ∧
        Nat.card (⁅X,Z R a⁆ ⊓ H₀ : Subgroup (FreeAmalgam R))=2^n ∧
        ∀ y ∈ Z R a ⊓ centralizer (X : Set (FreeAmalgam R)),
          (∃ b ∈ Z R z, ⁅b,y⁆ ≠ 1) →
            ∃ b ∈ Z R z, ⁅b,y⁆ ∉ ⁅X,Z R a⁆) := by
  obtain ⟨P,B,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,hesc⟩ :=
    original_source_four_large_unequal_intersection h hshort hinner hnsyl g hb path hat hzt hcritical hne
  refine ⟨P,B,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,?_⟩
  intro hescape
  obtain ⟨hn,hfull,hfull',hIcard⟩ := hesc hescape
  refine ⟨hn,hfull,hfull',hIcard,?_⟩
  intro y hy hyn
  apply original_source_four_large_full_hyperplane_value_escape h hshort hinner hnsyl g hb path hat hzt
    hcritical P hP hpoint hi hescape hfull ?_ hn y hy hyn
  let X := Z R z ⊓ centralizer (P : Set (FreeAmalgam R))
  let A := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
  let := g.Z_elementary (by omega : 0 < g.b R) z path.end_color
  have hHZ : ⁅Z R z,P⁆ ≤ Z R z := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp
      ((hP.trans (show Q R t ≤ stabilizer R z from fun _ hx => hx.2 _ (adjacent_symm R hzt))).trans (Z_normalized R z))
  have hXZ : ⁅X,B⁆ ≤ Z R z := (le_sup_left.trans hjoin.ge).trans hHZ
  have hnorm : A ≤ normalizer ((⁅X,B⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) :=
    (inf_le_left.trans (U_le_Z z)).trans
      ((Z R z).le_centralizer.trans (centralizer_le hXZ)) |>.trans
        (Subgroup.centralizer_le_normalizer _)
  rw [hjoin,card_sup_eq_mul_of_normalizes_of_disjoint _ _ hnorm hdis,hcard,hfull',pow_two]

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
