module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourRadicalGeneration
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourEscape
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourRootSelection

/-!
# Root selection in the original full-attachment comparison

The full covering kernel is a field line. Noncontainment of this line
forces disjointness; a nonzero movement-intersection vector then selects
a long-root element with all displacement values in that intersection.
The original radical factorization places this element in the opposite
hyperplane, contradicting the second-field obstruction.

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
private theorem full_plane_fixed_movement_kernel_power
    {z t : Vertex R}
    (cv : SaturatedDistanceTwo.RadicalPlaneCover R (originalMovedSection h) n z t)
    (hfull : Nat.card (U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) :
      Subgroup (FreeAmalgam R))=2^n)
    (P T : Subgroup (FreeAmalgam R)) (hP : P ≤ Q R t) (hT : T ≤ Q R t) :
    ∃ r : ℕ, Nat.card (⁅T,U R z ⊓ centralizer (P : Set (FreeAmalgam R))⁆ ⊓
      (U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))) :
        Subgroup (FreeAmalgam R))=(2^n)^r := by
  let p := MovedSection.coverProjection (originalMovedSection h) cv.equiv
  have hk : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map cv.embedding=
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
    apply le_antisymm
    · rintro v ⟨w,hw,rfl⟩
      exact ⟨cv.range_eq ▸ ⟨w,rfl⟩,(cv.kernel _).mp hw⟩
    · rintro v ⟨hv,hc⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hv
      exact ⟨w,(cv.kernel _).mpr hc,rfl⟩
  have hFc : Nat.card cv.field.Carrier=2^n := cv.field.card_eq.trans (congrArg (2^·) cv.degree)
  have hc : Nat.card p.toLinearMap.ker=Nat.card cv.field.Carrier := by
    rw [←embedded_cover_kernel_card p cv.embedding cv.injective,hk,hfull,hFc]
  simpa only [cv.range_eq,hk,hFc] using full_cover_fixed_movement_kernel_power p cv.cover hc
    cv.embedding cv.injective P T
    (cv.actor.comp (inclusion hP)) (cv.actor.comp (inclusion hT))
    (fun x w => cv.actor_conjugation (inclusion hP x) w)
    (fun x w => cv.actor_conjugation (inclusion hT x) w)

omit hshort hinner hnsyl in
/-- A full cover supplies an actual root element whose nontrivial displacement
lies in the hyperplane movement. The full attachment and section-centralizer
complement are the two excluded lines; the supplied plane marking is retained. -/
theorem plane_cover_hyperplane_root_element
    {z t : Vertex R}
    (cv : SaturatedDistanceTwo.RadicalPlaneCover R (originalMovedSection h) n z t)
    (k : Sp cv.field.Carrier)
    (hk : ((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).range.map
      (MulAut.conj k).toMonoidHom=planeRadicalAmbient)
    (P B T : Subgroup (FreeAmalgam R)) (hP : P ≤ Q R t) (hT : T ≤ Q R t)
    (hpoint : P=Q R t ⊓ centralizer
      (U R z ⊓ centralizer (P : Set (FreeAmalgam R)) : Set (FreeAmalgam R)))
    (hfix : ∀ w : (originalMovedSection h).space.toSubmodule,
      cv.embedding (Multiplicative.ofAdd w) ∈ centralizer (P : Set (FreeAmalgam R)) ↔
        (k • MovedSection.coverProjection (originalMovedSection h) cv.equiv w) (.inr 0)=0)
    (hmem : ∀ b : FreeAmalgam R, b ∈ B ↔ b ∈ Q R t ∧
      ∀ x ∈ U R z ⊓ centralizer (P : Set (FreeAmalgam R)),
        ⁅b,x⁆ ∈ ⁅P,U R z⁆)
    (hfull : Nat.card (U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) :
      Subgroup (FreeAmalgam R))=2^n)
    (hne : (⁅T,U R z ⊓ centralizer (P : Set (FreeAmalgam R))⁆ ⊓
      ⁅P,U R z⁆ : Subgroup (FreeAmalgam R)) ≠ ⊥)
    (hnot : ¬ U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) ≤
      ⁅T,U R z ⊓ centralizer (P : Set (FreeAmalgam R))⁆)
    (hcomp : Disjoint ⁅T,U R z ⊓ centralizer (P : Set (FreeAmalgam R))⁆
      ⁅U R z ⊓ centralizer (P : Set (FreeAmalgam R)),B⁆) :
    ∃ y ∈ P, (∃ u ∈ U R z, ⁅y,u⁆ ≠ 1) ∧
      ∀ u ∈ U R z, ⁅y,u⁆ ∈ ⁅T,U R z ⊓ centralizer (P : Set (FreeAmalgam R))⁆ := by
  let p := MovedSection.coverProjection (originalMovedSection h) cv.equiv
  let M := ⁅T,U R z ⊓ centralizer (P : Set (FreeAmalgam R))⁆
  let A := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
  have hkernel : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map cv.embedding=A := by
    apply le_antisymm
    · rintro v ⟨w,hw,rfl⟩
      exact ⟨cv.range_eq ▸ ⟨w,rfl⟩,(cv.kernel _).mp hw⟩
    · rintro v ⟨hv,hc⟩
      obtain ⟨w,rfl⟩ := cv.range_eq.symm ▸ hv
      exact ⟨w,(cv.kernel _).mpr hc,rfl⟩
  have hFc : Nat.card cv.field.Carrier=2^n := cv.field.card_eq.trans (congrArg (2^·) cv.degree)
  have hc : Nat.card p.toLinearMap.ker=Nat.card cv.field.Carrier := by
    rw [←embedded_cover_kernel_card p cv.embedding cv.injective,hkernel,hfull,hFc]
  have hlarge : 2 < Nat.card cv.field.Carrier := by
    rw [hFc]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.nonbinary
  obtain ⟨r,hr⟩ := full_plane_fixed_movement_kernel_power h cv hfull P T hP hT
  have hdis : Disjoint M A := by
    apply disjoint_iff.mpr
    apply Subgroup.card_eq_one.mp
    by_cases hzero : r=0
    · simpa only [hzero,pow_zero] using hr
    · exfalso
      let := finite_Z R z
      let : Finite A := Finite.of_injective (inclusion (inf_le_left.trans (U_le_Z z))) (inclusion_injective _)
      have hlow : 2^n ≤ (2^n)^r := by
        simpa only [pow_one] using Nat.pow_le_pow_right (by positivity : 0 < 2^n)
          (Nat.one_le_iff_ne_zero.mpr hzero)
      have he : M ⊓ A=A := Subgroup.eq_of_le_of_card_ge inf_le_right
        (by rw [hr,hfull]; exact hlow)
      exact hnot (he.ge.trans inf_le_left)
  simpa only [cv.range_eq] using marked_root_selection hlarge p cv.cover hc
    cv.embedding cv.injective (Q R t) cv.actor cv.actor_conjugation k hk P B T hP hT
    (by simpa only [cv.range_eq] using hpoint) hfix
    (by simpa only [cv.range_eq] using hmem) (by simpa only [cv.range_eq] using hne)
    (by simpa only [cv.range_eq,hkernel] using hdis) (by simpa only [cv.range_eq] using hcomp)

omit hshort hinner hnsyl in
/-- The earlier marked hyperplane geometry, with the original covering
map and complete kernel retained. This predicate contains no attachment
comparison conclusion. It provides a small application boundary for the
literal closure quotient. -/
@[expose] def HasOriginalMarkedHyperplane (z t : Vertex R)
    (P B : Subgroup (FreeAmalgam R)) : Prop :=
  ∃ cv : SaturatedDistanceTwo.RadicalPlaneCover R (originalMovedSection h) n z t,
  ∃ k : Sp cv.field.Carrier,
    ((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).range.map
      (MulAut.conj k).toMonoidHom=planeRadicalAmbient ∧
    P ≤ Q R t ∧ B ≤ Q R t ∧
    P=Q R t ⊓ centralizer
      (U R z ⊓ centralizer (P : Set (FreeAmalgam R)) : Set (FreeAmalgam R)) ∧
    (∀ w : (originalMovedSection h).space.toSubmodule,
      cv.embedding (Multiplicative.ofAdd w) ∈ centralizer (P : Set (FreeAmalgam R)) ↔
        (k • MovedSection.coverProjection (originalMovedSection h) cv.equiv w) (.inr 0)=0) ∧
    (∀ b : FreeAmalgam R, b ∈ B ↔ b ∈ Q R t ∧
      ∀ x ∈ U R z ⊓ centralizer (P : Set (FreeAmalgam R)),
        ⁅b,x⁆ ∈ ⁅P,U R z⁆)

/-- The marked root selection closes the full-attachment noncontainment
subcase of the escaping comparison. The nontrivial intersection, disjoint
complement and unequal root movement are the preceding source-(4) premises. -/
theorem original_source_four_large_marked_attachment_le
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (P B : Subgroup (FreeAmalgam R))
    (hmarked : HasOriginalMarkedHyperplane h z t P B)
    (hi : (Z R z ⊓ centralizer (P : Set (FreeAmalgam R))).relIndex (Z R z)=2^n)
    (hescape : ¬ Z R a ⊓ centralizer
      (Z R z ⊓ centralizer (P : Set (FreeAmalgam R)) : Set (FreeAmalgam R)) ≤ Q R z)
    (hfull : Nat.card (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) :
      Subgroup (FreeAmalgam R))=2^n)
    (hHcard : Nat.card (⁅Z R z,P⁆ : Subgroup (FreeAmalgam R))=(2^n)^2)
    (hMnot : ¬ ⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),Z R a⁆ ≤ ⁅Z R z,P⁆)
    (hmeet : (⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),Z R a⁆ ⊓
      ⁅Z R z,P⁆ : Subgroup (FreeAmalgam R)) ≠ ⊥)
    (hcomp : Disjoint ⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),Z R a⁆
      ⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),B⁆) :
    U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) ≤
      ⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),Z R a⁆ := by
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  obtain ⟨cv,k,hk,hP,hB,hpoint,hfix,hmem⟩ := hmarked
  classical
  by_contra hnot
  let X := Z R z ⊓ centralizer (P : Set (FreeAmalgam R))
  let X₀ := U R z ⊓ centralizer (P : Set (FreeAmalgam R))
  let C := Z R t
  let M := ⁅X,Z R a⁆
  let Y := Z R a ⊓ centralizer (X : Set (FreeAmalgam R))
  have hZaT : Z R a ≤ Q R t :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)).trans
      ((omegaCenter_le _).trans (Q_le_adjacent_h R ht hat))
  have hYT : Y ≤ Q R t := inf_le_left.trans hZaT
  have hCT : C ≤ centralizer (Q R t : Set (FreeAmalgam R)) :=
    midpoint_centralizes_radical path.end_color hzt
  have hCZ : C ≤ Z R z := Sp4Four.edge_Z_le_endpoint R path.end_color hzt
  let := g.Z_elementary (by omega : 0 < g.b R) z path.end_color
  have hCU : C ≤ normalizer (U R z : Set (FreeAmalgam R)) :=
    (hCZ.trans ((Z R z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCX : C ≤ normalizer (X₀ : Set (FreeAmalgam R)) :=
    (hCZ.trans ((Z R z).le_centralizer.trans
      (centralizer_le (inf_le_left.trans (U_le_Z z))))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hgen := original_Z_eq_moving_sup_edge h hshort hinner g hb path.end_color hzt
  have hX : X=X₀ ⊔ C := by
    dsimp only [X,X₀]
    rw [hgen,sup_comm (U R z),inf_centralizer_sup_of_centralizing C (U R z) P
        hCU (hCT.trans (centralizer_le hP)),sup_comm]
  have hM : M=⁅Z R a,X₀⁆ := by
    rw [show M=⁅X,Z R a⁆ from rfl,commutator_comm,hX]
    exact movement_central_supplement X₀ C (Q R t) (Z R a) hCX hCT hZaT
  have hH : ⁅Z R z,P⁆=⁅P,U R z⁆ := by
    rw [commutator_comm,hgen]
    exact movement_central_supplement (U R z) C (Q R t) P hCU hCT hP
  have hXB : ⁅X,B⁆=⁅X₀,B⁆ := by
    rw [commutator_comm _ B,hX,movement_central_supplement X₀ C (Q R t) B hCX hCT hB,commutator_comm]
  have hpointZ : P=Q R t ⊓ centralizer (X : Set (FreeAmalgam R)) := by
    apply le_antisymm
    · refine le_inf hP ?_
      rw [hX]
      apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff.mp (hpoint.le.trans inf_le_right)) (hCT.trans (centralizer_le hP))
    · exact (inf_le_inf_left _ (centralizer_le (show X₀ ≤ X from hX ▸ le_sup_left))).trans hpoint.ge
  have hfull' := (original_source_four_large_attachment_card_eq h hshort hinner hnsyl g hb path hat hzt hcritical).symm.trans hfull
  obtain ⟨b,hbP,⟨u,hu,hune⟩,hval⟩ := plane_cover_hyperplane_root_element h cv k hk P B
    (Z R a) hP hZaT hpoint hfix hmem hfull'
    (by change (⁅Z R a,X₀⁆ ⊓ ⁅P,U R z⁆ : Subgroup (FreeAmalgam R)) ≠ ⊥
        rw [←hM,←hH]; exact hmeet)
    (by change ¬ U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) ≤ ⁅Z R a,X₀⁆
        rw [←hM]; exact hnot)
    (by change Disjoint ⁅Z R a,X₀⁆ ⁅X₀,B⁆
        rw [←hM,←hXB]; exact hcomp)
  have hPY : P=Q R z ⊔ Y :=
    (original_source_four_large_escaping_hyperplane h hshort hinner hnsyl g hb path hat hzt
      hcritical P hP hpointZ hi hescape).2.2.1
  have hnorm : Y ≤ normalizer (Q R z : Set (FreeAmalgam R)) :=
    (hYT.trans (show Q R t ≤ stabilizer R z from fun _ hx => hx.2 _ (adjacent_symm R hzt))).trans (Q_normalized R z)
  rw [hPY,←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hnorm] at hbP
  obtain ⟨q,hq,y,hy,rfl⟩ := hbP
  have hQU : Q R z ≤ centralizer (U R z : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp ((U_le_Z z).trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q R z path.end_color)))
  have hYUn : Y ≤ normalizer (U R z : Set (FreeAmalgam R)) :=
    (hYT.trans (show Q R t ≤ stabilizer R z from fun _ hx => hx.2 _ (adjacent_symm R hzt))).trans (U_normalized z)
  have he (v : FreeAmalgam R) (hv : v ∈ U R z) : ⁅q*y,v⁆=⁅y,v⁆ := by
    have hm : ⁅y,v⁆ ∈ U R z :=
      (le_normalizer_iff_commutator_le_right.mp hYUn) (commutator_mem_commutator hy hv)
    have hh := hQU hq _ hm
    rw [commutatorElement_mul_left_eq_conj_mul,←hh,mul_inv_cancel_right,
      commutatorElement_eq_one_iff_commute.mpr (hQU hq v hv).symm,mul_one]
  have hune' : ⁅u,y⁆ ≠ 1 := by
    intro hh
    apply hune
    rw [he u hu,←commutatorElement_inv,hh,inv_one]
  have hvalues (v : FreeAmalgam R) (hv : v ∈ Z R z) : ⁅v,y⁆ ∈ M := by
    rw [hgen,←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hCU] at hv
    obtain ⟨w,hw,s,hs,rfl⟩ := hv
    have hys : Commute y s := hCT hs y (hYT hy)
    have hm : ⁅y,w⁆ ∈ M := by
      rw [←he w hw,hM]
      exact hval w hw
    have hh : ⁅y,w*s⁆ ∈ M := by
      rw [commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_eq_one_iff_commute.mpr hys]
      simpa only [mul_one,mul_inv_cancel_right] using hm
    rw [←commutatorElement_inv]
    exact M.inv_mem hh
  obtain ⟨v,hv,hvn⟩ := original_source_four_large_full_hyperplane_value_escape h hshort hinner hnsyl g hb path hat hzt hcritical P hP hpointZ hi hescape hfull hHcard hMnot y hy
      ⟨u,U_le_Z z hu,hune'⟩
  exact hvn (hvalues v hv)


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
