module
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourPlane
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourHyperplane
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourHyperplane

/-!
# Marked hyperplanes in the original large critical-image case

Use the original plane action to select a natural hyperplane X. Its
pointwise fixer P and section centralizer B are literal subgroups of the
common original radical. The displacement H = [Z,P] is the product of the
whole fixed attachment and A = [X,B], with A of order q and trivial
intersection with that attachment. The coordinate criterion retains the
original cover projection and any supplied plane marking. Adjoining the
central midpoint supplement gives the full-center version of the source
calculation, including containment in the critical displacement.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(4), printed p.875,
the opening hyperplane construction in the larger-image case. The internal
import reuses the generic marked plane-cover calculation only. The original
odd-index witness supplies the actual plane action in SourceFourPlane.
-/

public noncomputable section
open Matrix Subgroup Theory.GroupTheory Representation Representation.OneCohomology Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open Representation.SymplecticFourOrthogonalCover
open scoped commutatorElement IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

/-- For each supplied plane marking, the corresponding natural hyperplane's
section centralizer moves it in a field-sized complement to the whole attachment.
The coordinate criterion uses the original projection and the specified marking. -/
theorem original_plane_cover_hyperplane_attachment
    {z t : Vertex R}
    (cv : SaturatedDistanceTwo.RadicalPlaneCover R (originalMovedSection h) n z t)
    (k : Sp cv.field.Carrier)
    (hk : ((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).range.map
      (MulAut.conj k).toMonoidHom=planeRadicalAmbient) :
    ∃ P B : Subgroup (FreeAmalgam R), P ≤ Q R t ∧ B ≤ Q R t ∧
      P=Q R t ⊓ centralizer
        (U R z ⊓ centralizer (P : Set (FreeAmalgam R)) : Set (FreeAmalgam R)) ∧
      (centralizer (P : Set (FreeAmalgam R))).relIndex (U R z)=2^n ∧
      (∀ w : (originalMovedSection h).space.toSubmodule,
        cv.embedding (Multiplicative.ofAdd w) ∈ centralizer (P : Set (FreeAmalgam R)) ↔
          (k • MovedSection.coverProjection (originalMovedSection h) cv.equiv w) (.inr 0)=0) ∧
      (∀ b : FreeAmalgam R, b ∈ B ↔ b ∈ Q R t ∧
        ∀ x ∈ U R z ⊓ centralizer (P : Set (FreeAmalgam R)),
          ⁅b,x⁆ ∈ ⁅P,U R z⁆) ∧
      Disjoint ⁅U R z ⊓ centralizer (P : Set (FreeAmalgam R)),B⁆
        (U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))) ∧
      Nat.card (⁅U R z ⊓ centralizer (P : Set (FreeAmalgam R)),B⁆ :
        Subgroup (FreeAmalgam R))=2^n ∧
      ⁅P,U R z⁆ =
        ⁅U R z ⊓ centralizer (P : Set (FreeAmalgam R)),B⁆ ⊔
          (U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))) := by
  have hEc : Nat.card cv.field.Carrier=2^n :=
    cv.field.card_eq.trans (congrArg (2^·) cv.degree)
  have hlarge : 2 < Nat.card cv.field.Carrier := by
    rw [hEc]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.nonbinary
  let p := MovedSection.coverProjection (originalMovedSection h) cv.equiv
  have hker : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map cv.embedding =
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
    apply le_antisymm
    · rintro x ⟨w,hw,rfl⟩
      exact ⟨cv.range_eq ▸ ⟨w,rfl⟩,(cv.kernel _).mp hw⟩
    · rintro x ⟨hx,hc⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hx
      exact ⟨w,(cv.kernel _).mpr hc,rfl⟩
  simpa only [cv.range_eq,hEc,hker] using
    SaturatedDistanceTwo.plane_hyperplane hlarge p cv.cover cv.embedding cv.injective
      (Q R t) cv.actor cv.actor_conjugation k hk

omit [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem movement_central_supplement
    {G : Type*} [Group G] (U C Y A : Subgroup G)
    (hCU : C ≤ normalizer (U : Set G)) (hCY : C ≤ centralizer (Y : Set G))
    (hAY : A ≤ Y) : ⁅A,U ⊔ C⁆=⁅A,U⁆ := by
  apply le_antisymm ?_ (commutator_mono le_rfl le_sup_left)
  apply commutator_le.mpr
  intro b hb x hx
  rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hCU] at hx
  obtain ⟨u,hu,c,hc,rfl⟩ := hx
  have hbc : Commute b c := hCY hc b (hAY hb)
  rw [commutatorElement_mul_right_eq_mul_conj,commutatorElement_eq_one_iff_commute.mpr hbc]
  simpa only [mul_one,mul_inv_cancel_right] using commutator_mem_commutator hb hu

variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
variable (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
  (R.subgroupOf K).map (componentProjection h))
include hshort hinner hnsyl

/-- The full Z-hyperplane decomposition in the large critical-image branch
of MS93 (3.7)(4). Both centralizers are literal subgroups of the common radical;
the field-sized displacement complements the complete fixed attachment. -/
theorem original_source_four_large_hyperplane_attachment
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a)) :
    ∃ P B : Subgroup (FreeAmalgam R),
      let X := Z R z ⊓ centralizer (P : Set (FreeAmalgam R))
      let H₀ := ⁅Z R z,P⁆
      let A₀ := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
      Q R z ≤ P ∧ P ≤ Q R t ∧ B ≤ Q R t ∧
      P=Q R t ⊓ centralizer (X : Set (FreeAmalgam R)) ∧
      X.relIndex (Z R z)=2^n ∧
      Z R t ≤ X ∧ ⁅Z R a,Z R z⁆ ≤ X ∧
      (∀ b : FreeAmalgam R, b ∈ B ↔ b ∈ Q R t ∧ ∀ x ∈ X, ⁅b,x⁆ ∈ H₀) ∧
      Disjoint ⁅X,B⁆ A₀ ∧ Nat.card (⁅X,B⁆ : Subgroup (FreeAmalgam R))=2^n ∧
      H₀=⁅X,B⁆ ⊔ A₀ ∧ H₀ ≤ ⁅Z R a,Z R z⁆ := by
  obtain ⟨⟨cv⟩,_,_,_⟩ := original_source_four_large_plane_cover h hshort hinner hnsyl g hb path hat hzt hcritical
  obtain ⟨k,hk⟩ := cv.plane_image
  obtain ⟨P,B,hP,hB,hpoint,hindex,_,hmem,hdis,hcard,hjoin⟩ :=
    original_plane_cover_hyperplane_attachment h cv k hk
  let C := Z R t
  let V := U R z
  let X₀ := V ⊓ centralizer (P : Set (FreeAmalgam R))
  let X₁ := Z R z ⊓ centralizer (P : Set (FreeAmalgam R))
  let Y := Q R t
  have hgen : Z R z=V ⊔ C :=
    original_Z_eq_moving_sup_edge h hshort hinner g hb path.end_color hzt
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hzt (path.end_color.trans he.symm)
  have hC : C=omegaCenter Y := by simp [C,Y,Z,ht,edgeOmega]
  have hCY : C ≤ centralizer (Y : Set (FreeAmalgam R)) := by
    rw [hC]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  let := g.Z_elementary (by omega : 0 < g.b R) z path.end_color
  have hCZ : C ≤ Z R z := Sp4Four.edge_Z_le_endpoint R path.end_color hzt
  have hCU : C ≤ normalizer (V : Set (FreeAmalgam R)) :=
    (hCZ.trans ((Z R z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCX : C ≤ normalizer (X₀ : Set (FreeAmalgam R)) :=
    (hCZ.trans ((Z R z).le_centralizer.trans
      (centralizer_le (inf_le_left.trans (U_le_Z z))))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hCP : C ≤ centralizer (P : Set (FreeAmalgam R)) := hCY.trans (centralizer_le hP)
  have hX : X₁=X₀ ⊔ C := by
    dsimp only [X₁,X₀]
    rw [hgen,sup_comm V C,inf_centralizer_sup_of_centralizing C V P hCU hCP,sup_comm]
  have hHZ : ⁅Z R z,P⁆=⁅P,V⁆ := by
    rw [commutator_comm,hgen]
    exact movement_central_supplement V C Y P hCU hCY hP
  have hXB : ⁅X₁,B⁆=⁅X₀,B⁆ := by
    rw [commutator_comm _ B,hX,movement_central_supplement X₀ C Y B hCX hCY hB,
      commutator_comm]
  have hpointZ : P=Y ⊓ centralizer (X₁ : Set (FreeAmalgam R)) := by
    apply le_antisymm
    · refine le_inf hP ?_
      rw [hX]
      apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff.mp (hpoint.le.trans inf_le_right)) hCP
    · exact (inf_le_inf_left Y (centralizer_le
        (show X₀ ≤ X₁ from hX ▸ le_sup_left))).trans hpoint.ge
  have hQ : Q R z ≤ P := by
    rw [hpointZ]
    apply le_inf (Q_le_adjacent_h R ht hzt)
    exact le_centralizer_iff.mp
      (inf_le_left.trans (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R z path.end_color)))
  have hi : X₁.relIndex (Z R z)=2^n := by
    let := finite_Z R z
    let : Finite X₁ := Finite.of_injective (inclusion (show X₁ ≤ Z R z from inf_le_left))
      (inclusion_injective _)
    have hVX : V ⊔ X₁=Z R z := by
      rw [hX,←sup_assoc,sup_eq_left.mpr (show X₀ ≤ V from inf_le_left),←hgen]
    have hXU : X₁ ≤ normalizer (V : Set (FreeAmalgam R)) :=
      (inf_le_left.trans ((Z R z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
        (Subgroup.centralizer_le_normalizer _)
    rw [←hVX,relIndex_sup_of_normalizes V X₁ hXU]
    have hInf : X₁ ⊓ V=X₀ := by
      ext x
      exact ⟨fun hx => ⟨hx.2,hx.1.2⟩,fun hx => ⟨⟨U_le_Z z hx.1,hx.2⟩,hx.1⟩⟩
    rw [←inf_relIndex_right,hInf,inf_relIndex_left]
    exact hindex
  have hCX₁ : C ≤ X₁ := le_inf hCZ hCP
  have hZaQ : Z R a ≤ Q R a :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)).trans
      (omegaCenter_le _)
  have hcommon : ⁅Z R a,Z R z⁆ ≤ C := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hZaQ).trans
      (original_source_two_midpoint_containment h hshort hinner g hb hnsyl path hat hzt)
  refine ⟨P,B,hQ,hP,hB,hpointZ,hi,hCX₁,hcommon.trans hCX₁,?_,?_,?_,?_,?_⟩
  · intro b
    rw [hmem]
    constructor
    · rintro ⟨hb,hm⟩
      refine ⟨hb,fun x hx => ?_⟩
      change x ∈ X₁ at hx
      rw [hX,←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hCX] at hx
      obtain ⟨u,hu,v,hv,rfl⟩ := hx
      have hbv : Commute b v := hCY hv b hb
      rw [hHZ,commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_eq_one_iff_commute.mpr hbv]
      simpa only [mul_one,mul_inv_cancel_right] using hm u hu
    · rintro ⟨hb,hm⟩
      refine ⟨hb,fun x hx => ?_⟩
      rw [←hHZ]
      apply hm x
      change x ∈ X₁
      rw [hX]
      exact mem_sup_left hx
  · rw [hXB]
    exact hdis
  · rw [hXB]
    exact hcard
  · rw [hHZ,hXB]
    exact hjoin
  · rw [commutator_comm]
    exact (commutator_mono hP le_rfl).trans_eq
      (original_source_four_large_full_movement h hshort hinner hnsyl g hb path hat hzt hcritical)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
