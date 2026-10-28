module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFiveCore
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourPlane
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFiveCore
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFiveCentralizer

/-!
# Original plane-radical centralizer counts in MS93 (3.7)(5)

The full original center is its moving layer times the midpoint center.
A noncentral vector therefore has a plane-radical centralizer with image
of order q. The whole-core dual cover identifies its omega displacement
modulo the entire fixed attachment with its natural displacement.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(5), pp.875--876.
The generic cover computations are reused with the literal original action.
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
open SaturatedDistanceTwo (embedded_plane_centralizer_index embedded_commutator_central_index
  central_supplement_fixed_index)
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
include h hshort hinner

private theorem moving_factor_not_central
    (g : Geometry R) (hb : g.b R=2)
    {a t : Vertex R} (ha : color R a=false)
    (hat : Adjacent R a t)
    (x : FreeAmalgam R) (hx : x ∈ Z R a) (hne : x ∉ Z R t) :
    ∃ u ∈ U R a,
      Q R t ⊓ centralizer ({x} : Set (FreeAmalgam R))=
        Q R t ⊓ centralizer ({u} : Set (FreeAmalgam R)) ∧
      u ∉ centralizer (Q R t : Set (FreeAmalgam R)) := by
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (ha.trans he.symm)
  have hZt : Z R t=omegaCenter (Q R t) := by simp [Z,ht,edgeOmega]
  have hcentral : Z R t ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
    rw [hZt]
    exact fun v hv => (mem_omegaCenter_iff.mp hv).2.2
  have hZX : Z R a ≤ X R a :=
    g.omega_bound a ha (by rw [g.distance_constant a ha]; change 0<g.b R; omega)
  have hUQ : U R a ≤ Q R a := (U_le_Z a).trans (hZX.trans (omegaCenter_le _))
  have hUn : U R a ≤ normalizer (Z R t : Set (FreeAmalgam R)) :=
    ((hUQ.trans (original_core_le_edge R ha hat)).trans (le_centralizer_iff.mp hcentral)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hx' := hx
  rw [original_Z_eq_moving_sup_edge h hshort hinner g hb ha hat,←SetLike.mem_coe,
    coe_mul_of_left_le_normalizer_right _ _ hUn] at hx'
  obtain ⟨u,hu,v,hv,rfl⟩ := hx'
  refine ⟨u,hu,?_,?_⟩
  · ext b
    simp only [mem_inf,mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hb,hbcomm⟩
      refine ⟨hb,?_⟩
      apply mul_right_cancel (b := v)
      calc
        b*u*v = b*(u*v) := mul_assoc _ _ _
        _ = u*v*b := hbcomm
        _ = u*b*v := by rw [mul_assoc,←hcentral hv b hb,←mul_assoc]
    · rintro ⟨hb,hbcomm⟩
      refine ⟨hb,?_⟩
      calc
        b*(u*v) = (b*u)*v := (mul_assoc _ _ _).symm
        _ = (u*b)*v := by rw [hbcomm]
        _ = (u*v)*b := by rw [mul_assoc,hcentral hv b hb,←mul_assoc]
  · intro hfix
    apply hne
    rw [hZt]
    exact mem_omegaCenter_iff.mpr ⟨(original_core_le_edge R ha hat) (omegaCenter_le _ (hZX hx)),
      (mem_omegaCenter_iff.mp (hZX hx)).2.1,
      (centralizer (Q R t : Set (FreeAmalgam R))).mul_mem hfix (hcentral hv)⟩

/-- The actual element centralizer in a full plane radical has field order
modulo the entire endpoint core and moves exactly q cosets of U. -/
theorem original_plane_cover_element_centralizer
    (g : Geometry R) (hb : g.b R=2)
    {a t : Vertex R} (ha : color R a=false)
    (hat : Adjacent R a t)
    (cv : SaturatedDistanceTwo.RadicalPlaneCover R (originalMovedSection h) n a t)
    (x : FreeAmalgam R) (hx : x ∈ Z R a) (hne : x ∉ Z R t) :
    let C := Q R t ⊓ centralizer ({x} : Set (FreeAmalgam R))
    (Q R a).relIndex C=2^n ∧
      (centralizer (C : Set (FreeAmalgam R))).relIndex (U R a)=2^n := by
  obtain ⟨u,hu,hC,hnu⟩ := moving_factor_not_central h hshort hinner g hb ha hat x hx hne
  rcases cv with ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩,
    hTS,β,hβmark,hact,hαker,⟨k,hk⟩⟩
  have hc := embedded_plane_centralizer_index
    (MovedSection.coverAction (originalMovedSection h) e)
    (MovedSection.coverProjection (originalMovedSection h) e) he
    (U R a) (Q R t) (Q R a) j hj hjr β hact hαker k hk u hu hnu
  have hEc : Nat.card E.Carrier=2^n := E.card_eq.trans (congrArg (2^·) hE)
  dsimp only at hc ⊢
  rw [hEc] at hc
  rw [hC]
  exact hc

private theorem omega_displacement_attachment_index
    (g : Geometry R) (hb : g.b R=2)
    {a t : Vertex R} (ha : color R a=false)
    (hat : Adjacent R a t) (B : Subgroup (FreeAmalgam R)) (hBT : B ≤ Q R t) :
    (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))).relIndex
      ⁅X R a,B⁆ =
    (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))).relIndex
      ⁅U R a,B⁆ := by
  let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
  let D := fixedCore R a
  let M := ⁅U R a,B⁆
  let N := ⁅X R a,B⁆
  have hXQ : X R a ≤ Q R a := omegaCenter_le _
  have hZX := g.omega_bound a ha (by rw [g.distance_constant a ha]; change 0<g.b R; omega)
  have hUX : U R a ≤ X R a := (U_le_Z a).trans hZX
  have hMU : M ≤ U R a := by
    change ⁅U R a,B⁆ ≤ U R a
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp ((hBT.trans (original_edge_le_stabilizer R hat)).trans (U_normalized a))
  have hNU : N ≤ U R a := by
    change ⁅X R a,B⁆ ≤ U R a
    rw [commutator_comm]
    apply (commutator_mono (hBT.trans (original_edge_le_stabilizer R hat)) le_rfl).trans
    rw [←(original_stabilizer_eq_residual_sup_core h hinner ha).symm]
    apply commutator_sup_le_of_relative_normal (stabilizer R a)
      (Ltilde R a) (Q R a) (X R a) (U R a)
      (U_normalized a) (Ltilde_le_stabilizer _) (fun _ hx => hx.1)
    · rw [commutator_comm]
      exact (commutator_mono hXQ le_rfl).trans
        (short_original_core_eq_U h hshort ha).le
    · rw [commutator_comm]
      exact (commutator_eq_bot_iff_le_centralizer.mpr
        (show X R a ≤ centralizer (Q R a : Set (FreeAmalgam R)) from
          fun _ hx => (mem_omegaCenter_iff.mp hx).2.2)).le.trans bot_le
  have hMN : M ≤ N := commutator_mono hUX le_rfl
  have hUD : U R a ≤ centralizer (D : Set (FreeAmalgam R)) :=
    ((U_le_Z a).trans (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a ha))).trans
      (centralizer_le inf_le_left)
  have hbound : N ≤ M ⊔ A := by
    intro x hx
    have hprod := ((commutator_mono hXQ le_rfl).trans
      (original_whole_core_displacement_le h hshort hinner ha B (hBT.trans (original_edge_le_stabilizer R hat)))) hx
    change x ∈ M ⊔ D at hprod
    rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _
      ((hMU.trans hUD).trans (Subgroup.centralizer_le_normalizer _))] at hprod
    obtain ⟨v,hv,w,hw,rfl⟩ := hprod
    have hwU : w ∈ U R a := by
      have hh := (U R a).mul_mem ((U R a).inv_mem (hMU hv)) (hNU hx)
      simpa only [inv_mul_cancel_left] using hh
    exact mul_mem (mem_sup_left hv) (mem_sup_right ⟨hwU,hw.2⟩)
  let := finite_Z R a
  let : Finite (U R a) := Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  let : Finite N := Finite.of_injective (inclusion hNU) (inclusion_injective _)
  let : Finite A := Finite.of_injective
    (inclusion (show A ≤ U R a from inf_le_left)) (inclusion_injective _)
  let : Finite (M ⊔ A : Subgroup (FreeAmalgam R)) := Finite.of_injective
    (inclusion (sup_le hMU (show A ≤ U R a from inf_le_left))) (inclusion_injective _)
  let : IsElementaryAbelian 2 (U R a) := h.vertex_moving_elementary ha
  have hAM : A ≤ normalizer (M : Set (FreeAmalgam R)) :=
    ((show A ≤ U R a from inf_le_left).trans
      ((U R a).le_centralizer.trans (centralizer_le hMU))).trans
      (Subgroup.centralizer_le_normalizer _)
  exact le_antisymm
    ((relIndex_le_of_le_right hbound index_ne_zero_of_finite).trans_eq
      (relIndex_sup_of_normalizes M A hAM))
    (relIndex_le_of_le_right hMN index_ne_zero_of_finite)

private theorem plane_cover_omega_displacement_index
    (g : Geometry R) (hb : g.b R=2)
    {a t : Vertex R} (ha : color R a=false)
    (hat : Adjacent R a t)
    (cv : SaturatedDistanceTwo.RadicalPlaneCover R (originalMovedSection h) n a t)
    (B : Subgroup (FreeAmalgam R)) (hBT : B ≤ Q R t) :
    (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))).relIndex
      ⁅X R a,B⁆ = (centralizer (B : Set (FreeAmalgam R))).relIndex (U R a) := by
  rw [omega_displacement_attachment_index h hshort hinner g hb ha hat B hBT,commutator_comm]
  rcases cv with ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩,
    hTS,β,hβmark,hact,hαker,hplane⟩
  apply embedded_commutator_central_index
    (MovedSection.coverAction (originalMovedSection h) e)
    (MovedSection.coverProjection (originalMovedSection h) e) he
    (U R a) B _ j hj hjr (β.comp (inclusion hBT))
    (fun b w => hact (inclusion hBT b) w)
  intro w
  exact (hker w).trans ⟨fun hc => ⟨hjr ▸ ⟨_,rfl⟩,hc⟩,fun hc => hc.2⟩

variable (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
  (R.subgroupOf K).map (componentProjection h))
include hnsyl

/-- The full central-omega movement in the plane branch of source (5).
The quotient is by the complete attachment, not just its natural image. -/
theorem original_source_five_large_omega_displacement
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (x : FreeAmalgam R) (hx : x ∈ Z R a) (hne : x ∉ Z R t) :
    let C := Q R t ⊓ centralizer ({x} : Set (FreeAmalgam R))
    (Q R a).relIndex C=2^n ∧
      (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))).relIndex
        ⁅X R a,C⁆=2^n := by
  obtain ⟨⟨cv⟩,_⟩ := original_source_four_large_paired_geometry h hshort hinner hnsyl g hb path hat hzt hcritical
  have hc := original_plane_cover_element_centralizer h hshort hinner g hb path.start_color hat cv x hx hne
  exact ⟨hc.1,(plane_cover_omega_displacement_index h hshort hinner g hb path.start_color hat cv
    (Q R t ⊓ centralizer ({x} : Set (FreeAmalgam R))) inf_le_left).trans hc.2⟩

/-- The actual Q₂ centralizer count in the large critical-image branch,
with the plane cover constructed on the original nonsylow star. -/
theorem original_source_five_large_element_centralizer
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (x : FreeAmalgam R) (hx : x ∈ Z R a) (hne : x ∉ Z R t) :
    let C := Q R t ⊓ centralizer ({x} : Set (FreeAmalgam R))
    (Q R a).relIndex C=2^n ∧
      (centralizer (C : Set (FreeAmalgam R))).relIndex (U R a)=2^n ∧
      (centralizer (C : Set (FreeAmalgam R))).relIndex (Z R a)=2^n := by
  obtain ⟨⟨cv⟩,_⟩ := original_source_four_large_paired_geometry h hshort hinner hnsyl g hb path hat hzt hcritical
  have hc := original_plane_cover_element_centralizer h hshort hinner g hb path.start_color hat cv x hx hne
  refine ⟨hc.1,hc.2,?_⟩
  let C := Q R t ⊓ centralizer ({x} : Set (FreeAmalgam R))
  let := finite_Z R a
  let := g.Z_elementary (by omega) a path.start_color
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  have hcentral : Z R t ≤ centralizer (C : Set (FreeAmalgam R)) := by
    intro v hv b hbq
    have hv' : v ∈ omegaCenter (Q R t) := by simpa [Z,ht,edgeOmega] using hv
    exact (mem_omegaCenter_iff.mp hv').2.2 b hbq.1
  exact (central_supplement_fixed_index (U R a) (Z R t)
    (Z R a) C (U_le_Z a) (Sp4Four.edge_Z_le_endpoint R path.start_color hat)
    (original_Z_eq_moving_sup_edge h hshort hinner g hb path.start_color hat) hcentral).trans hc.2

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
