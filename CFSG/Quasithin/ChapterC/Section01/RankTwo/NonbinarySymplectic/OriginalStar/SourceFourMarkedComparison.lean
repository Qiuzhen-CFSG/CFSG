module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourMarkedIntersection
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourMarkedIntersection
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourEscape
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourMarkedComparison

/-!
# Excluding escaping hyperplane centralizers in the original radical

The opposite field-index centralizer gives a second marked hyperplane
without changing the original quotient action. Applying the two movement
intersection identities to the same pair would equate unequal complete
attachments. Thus the opposite centralizer lies in the endpoint core.
The final existence theorem constructs the marking from the original cover.

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

omit hnsyl in
/-- A field-index centralizer determines its actual dual marked hyperplane. -/
theorem plane_cover_dual_marked_hyperplane
    (g : Geometry R) (hb : g.b R=2)
    {z t : Vertex R} (hz : color R z=false)
    (hzt : Adjacent R z t)
    (cv : SaturatedDistanceTwo.RadicalPlaneCover R (originalMovedSection h) n z t)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ Q R t)
    (hi : (centralizer (A : Set (FreeAmalgam R))).relIndex (Z R z)=2^n) :
    ∃ P B : Subgroup (FreeAmalgam R),
      let Y := Z R z ⊓ centralizer (A : Set (FreeAmalgam R))
      HasOriginalMarkedHyperplane h z t P B ∧ P ≤ Q R t ∧
      P=Q R t ⊓ centralizer (Y : Set (FreeAmalgam R)) ∧
      Z R z ⊓ centralizer (P : Set (FreeAmalgam R))=Y := by
  let α := (commutator (Sp cv.field.Carrier)).subtype.comp cv.actor
  let β := cv.actor.comp (inclusion hA)
  let αA := α.comp (inclusion hA)
  have hd : Module.finrank cv.field.Carrier (displacementSpace αA.range)=1 := by
    have hh := plane_cover_full_fixed_index h hshort hinner g hb hz hzt cv A hA
    have hh' : 2^n=(2^n)^Module.finrank cv.field.Carrier (displacementSpace αA.range) := hi.symm.trans hh
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    exact Nat.pow_right_injective hq (hh'.symm.trans (pow_one _).symm)
  have hAT : αA.range ≤ α.range := by rintro _ ⟨a,rfl⟩; exact ⟨inclusion hA a,rfl⟩
  obtain ⟨k,hk,hdline⟩ := plane_line_marking
    (cv.field.card_eq.trans (congrArg (2^·) cv.degree)) h.nonbinary
    α.range αA.range hAT cv.plane_image hd
  let p := MovedSection.coverProjection (originalMovedSection h) cv.equiv
  have hfixA (w : (originalMovedSection h).space.toSubmodule) :
      cv.embedding (Multiplicative.ofAdd w) ∈ centralizer (A : Set (FreeAmalgam R)) ↔
        (k • p w) (.inr 0)=0 :=
    fixed_cover_marking p cv.cover cv.embedding cv.injective A β
      (fun a w => cv.actor_conjugation (inclusion hA a) w) k hdline w
  obtain ⟨P,B,hP,hB,hpoint,hindex,hfix,hmem,_⟩ := original_plane_cover_hyperplane_attachment h cv k hk
  have hm : HasOriginalMarkedHyperplane h z t P B := ⟨cv,k,hk,hP,hB,hpoint,hfix,hmem⟩
  have hUeq : U R z ⊓ centralizer (P : Set (FreeAmalgam R)) =
      U R z ⊓ centralizer (A : Set (FreeAmalgam R)) := by
    ext x
    constructor
    · rintro ⟨hx,hc⟩
      refine ⟨hx,?_⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hx
      exact (hfixA w.toAdd).mpr ((hfix w.toAdd).mp hc)
    · rintro ⟨hx,hc⟩
      refine ⟨hx,?_⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hx
      exact (hfix w.toAdd).mpr ((hfixA w.toAdd).mp hc)
  let C := Z R t
  have hCT : C ≤ centralizer (Q R t : Set (FreeAmalgam R)) :=
    midpoint_centralizes_radical hz hzt
  have hCZ : C ≤ Z R z := Sp4Four.edge_Z_le_endpoint R hz hzt
  let := g.Z_elementary (by omega : 0 < g.b R) z hz
  have hCU : C ≤ normalizer (U R z : Set (FreeAmalgam R)) :=
    (hCZ.trans ((Z R z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCP : C ≤ centralizer (P : Set (FreeAmalgam R)) := hCT.trans (centralizer_le hP)
  have hCA : C ≤ centralizer (A : Set (FreeAmalgam R)) := hCT.trans (centralizer_le hA)
  have hgen := original_Z_eq_moving_sup_edge h hshort hinner g hb hz hzt
  have hXP : Z R z ⊓ centralizer (P : Set (FreeAmalgam R)) =
      (U R z ⊓ centralizer (P : Set (FreeAmalgam R))) ⊔ C := by
    rw [hgen,sup_comm (U R z),inf_centralizer_sup_of_centralizing C
      (U R z) P hCU hCP,sup_comm]
  have hYA : Z R z ⊓ centralizer (A : Set (FreeAmalgam R)) =
      (U R z ⊓ centralizer (A : Set (FreeAmalgam R))) ⊔ C := by
    rw [hgen,sup_comm (U R z),inf_centralizer_sup_of_centralizing C
      (U R z) A hCU hCA,sup_comm]
  have heq : Z R z ⊓ centralizer (P : Set (FreeAmalgam R)) =
      Z R z ⊓ centralizer (A : Set (FreeAmalgam R)) := by rw [hXP,hYA,hUeq]
  refine ⟨P,B,hm,hP,?_,heq⟩
  apply le_antisymm
  · refine le_inf hP ?_
    rw [hYA,←hUeq]
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp (hpoint.le.trans inf_le_right)) hCP
  · have hle : U R z ⊓ centralizer (P : Set (FreeAmalgam R)) ≤
        Z R z ⊓ centralizer (A : Set (FreeAmalgam R)) := by
      rw [hYA,←hUeq]; exact le_sup_left
    exact (inf_le_inf_left _ (centralizer_le hle)).trans hpoint.ge


/-- The escaping-centralizer branch of source (4) is impossible when the
complete attachments differ. The opposite hyperplane is marked from its
actual field-linear fixed space, then the two intersection identities use
the same pair of hyperplanes and the original covering maps. -/
theorem original_source_four_large_marked_centralizer_le
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (hne : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) ≠
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)))
    (P B : Subgroup (FreeAmalgam R))
    (hmarked : HasOriginalMarkedHyperplane h z t P B) :
    Z R a ⊓ centralizer
      (Z R z ⊓ centralizer (P : Set (FreeAmalgam R)) : Set (FreeAmalgam R)) ≤ Q R z := by
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  by_contra hescape
  let X := Z R z ⊓ centralizer (P : Set (FreeAmalgam R))
  let Y := Z R a ⊓ centralizer (X : Set (FreeAmalgam R))
  let C := Z R t
  obtain ⟨hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,hBi⟩ :=
    marked_hyperplane_geometry h hshort hinner hnsyl g hb path hat hzt hcritical P B hmarked
  obtain ⟨hYi,_,hPY,hHY⟩ := original_source_four_large_escaping_hyperplane h hshort hinner hnsyl g hb path hat hzt hcritical P hP hpoint hi hescape
  have hzQ : Z R z ≤ Q R z :=
    (g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]; change 0 < g.b R; omega)).trans
      (omegaCenter_le _)
  have hXT : X ≤ Q R t := inf_le_left.trans (hzQ.trans (Q_le_adjacent_h R ht hzt))
  have hQU : Q R z ≤ centralizer (Z R z : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q R z path.end_color))
  have hYX : Z R z ⊓ centralizer (Y : Set (FreeAmalgam R))=X := by
    apply le_antisymm
    · apply le_inf inf_le_left
      apply le_centralizer_iff.mpr
      rw [hPY]
      exact sup_le (hQU.trans (centralizer_le inf_le_left))
        (le_centralizer_iff.mp (show Z R z ⊓ centralizer (Y : Set (FreeAmalgam R)) ≤
          centralizer (Y : Set (FreeAmalgam R)) from inf_le_right))
    · exact le_inf inf_le_left (le_centralizer_iff.mp (show Y ≤
        centralizer (X : Set (FreeAmalgam R)) from inf_le_right))
  obtain ⟨⟨cv⟩,_,hai,hzi,_⟩ := original_source_four_large_paired_geometry h hshort hinner hnsyl g hb path hat hzt hcritical
  obtain ⟨P',B',hm',hP',hpY,heY⟩ := plane_cover_dual_marked_hyperplane h hshort hinner g hb
    path.start_color hat cv X hXT (by rwa [inf_relIndex_left] at hYi)
  have hp' : P'=Q R t ⊓ centralizer
      (Z R a ⊓ centralizer (P' : Set (FreeAmalgam R)) : Set (FreeAmalgam R)) :=
    hpY.trans (congrArg (fun S : Subgroup (FreeAmalgam R) =>
      Q R t ⊓ centralizer (S : Set (FreeAmalgam R))) heY.symm)
  have hi' : (Z R a ⊓ centralizer (P' : Set (FreeAmalgam R))).relIndex
      (Z R a)=2^n := by rw [heY]; exact hYi
  obtain ⟨_,hzk,_,hreverse⟩ := original_source_four_large_midpoint_kernels h hshort hinner hnsyl g hb path hat hzt hcritical
  have hXnot : ¬ X ≤ Q R a := by
    intro hle
    have he : X=C := le_antisymm
      ((le_inf (show X ≤ Z R z from inf_le_left) hle).trans_eq hzk) hCX
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    change X.relIndex (Z R z)=2^n at hi
    rw [he,hzi] at hi
    nlinarith only [hq,hi]
  have hreverseX : Z R z ⊓ centralizer
      (Z R a ⊓ centralizer (P' : Set (FreeAmalgam R)) : Set (FreeAmalgam R))=X :=
    (congrArg (fun S : Subgroup (FreeAmalgam R) =>
      Z R z ⊓ centralizer (S : Set (FreeAmalgam R))) heY).trans hYX
  have hescape' : ¬ Z R z ⊓ centralizer
      (Z R a ⊓ centralizer (P' : Set (FreeAmalgam R)) : Set (FreeAmalgam R)) ≤ Q R a :=
    fun hle => hXnot (hreverseX.ge.trans hle)
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  have hr : (2^n)^2 ≤ (Q R a).relIndex (Z R z) := hreverse.ge
  have hA₀ := original_source_four_large_marked_attachment_intersection h hshort hinner hnsyl g hb path hat hzt hcritical hne P B hmarked hescape
  have hA₁ := original_source_four_large_marked_attachment_intersection h hshort hinner hnsyl g hb rev hzt hat hr (Ne.symm hne) P' B' hm' hescape'
  have hm := (original_source_four_large_escaping_hyperplane h hshort hinner hnsyl g hb rev hzt hat hr P' hP' hp' hi' hescape').2.2.2
  rw [heY] at hA₁
  change _=⁅Y,Z R z⁆ ⊓ ⁅Z R a,P'⁆ at hA₁
  have hmX : ⁅Z R a,P'⁆=⁅Z R a,X⁆ :=
    hm.trans (congrArg (fun S : Subgroup (FreeAmalgam R) => ⁅Z R a,S⁆) hreverseX)
  rw [hmX,commutator_comm Y (Z R z),←hHY,commutator_comm (Z R a) X] at hA₁
  exact hne (hA₁.trans ((inf_comm _ _).trans hA₀.symm))

/-- The source plane geometry supplies a genuine marked hyperplane whose
opposite centralizer lies in the endpoint core whenever the attachments differ.
The complete complement and original movement data are retained. -/
theorem original_source_four_large_unequal_nonescaping_hyperplane
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
      HasOriginalMarkedHyperplane h z t P B ∧ Q R z ≤ P ∧ P ≤ Q R t ∧ B ≤ Q R t ∧
      P=Q R t ⊓ centralizer (X : Set (FreeAmalgam R)) ∧
      X.relIndex (Z R z)=2^n ∧
      Z R t ≤ X ∧ ⁅Z R a,Z R z⁆ ≤ X ∧
      (∀ b : FreeAmalgam R, b ∈ B ↔ b ∈ Q R t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam R))=2^n ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z R a,Z R z⁆ ∧ B.relIndex (Q R t)=2^n ∧
      Z R a ⊓ centralizer (X : Set (FreeAmalgam R)) ≤ Q R z := by
  obtain ⟨P,B,hm,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,hBi,_⟩ :=
    original_source_four_large_unequal_marked_intersection h hshort hinner hnsyl g hb path hat hzt hcritical hne
  exact ⟨P,B,hm,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,hBi,
    original_source_four_large_marked_centralizer_le h hshort hinner hnsyl g hb path hat hzt hcritical hne P B hm⟩


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
