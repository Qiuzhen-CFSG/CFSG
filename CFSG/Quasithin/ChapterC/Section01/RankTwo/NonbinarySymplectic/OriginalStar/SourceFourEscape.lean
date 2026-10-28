module
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourHyperplane
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourEscape

/-!
# The escaping hyperplane centralizer in the original large-image case

Both original critical kernels are the full midpoint center. If the
opposite center's centralizer of the chosen hyperplane escapes the endpoint
core, it has field order modulo that core and fills the hyperplane fixer.
Thus it gives the full hyperplane displacement. The reciprocal action is
an actual long root, whose full-cover displacement contains the entire
opposite attachment and has index q over it.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(4), printed p.875,
the paragraph beginning with the escaping-centralizer assumption. The
internal import reuses generic cover and relative-index proofs; the
original radical and both complete fixed attachments are retained.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

omit [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem midpoint_centralizes_radical
    {z t : Vertex R} (hz : color R z=false)
    (hzt : Adjacent R z t) :
    Z R t ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hzt (hz.trans he.symm)
  rw [show Z R t=omegaCenter (Q R t) by simp [Z,ht,edgeOmega]]
  exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2

private theorem plane_cover_actor_card
    {z t : Vertex R}
    (cv : SaturatedDistanceTwo.RadicalPlaneCover R (originalMovedSection h) n z t)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ Q R t) :
    Nat.card (((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).comp
      (inclusion hA)).range=(Q R z).relIndex A := by
  rw [←index_ker,←MonoidHom.comap_ker,cv.actor_kernel,comap_inclusion_subgroupOf]
  rfl

variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
include hshort hinner

private theorem plane_cover_full_fixed_index
    (g : Geometry R) (hb : g.b R=2)
    {z t : Vertex R} (hz : color R z=false)
    (hzt : Adjacent R z t)
    (cv : SaturatedDistanceTwo.RadicalPlaneCover R (originalMovedSection h) n z t)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ Q R t) :
    (centralizer (A : Set (FreeAmalgam R))).relIndex (Z R z)=
      (2^n)^Module.finrank cv.field.Carrier (displacementSpace
        (((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).comp (inclusion hA)).range) := by
  let := g.Z_elementary (by omega : 0 < g.b R) z hz
  let := finite_Z R z
  have he := central_supplement_fixed_index (U R z) (Z R t) (Z R z) A
    (U_le_Z z) (Sp4Four.edge_Z_le_endpoint R hz hzt)
    (original_Z_eq_moving_sup_edge h hshort hinner g hb hz hzt)
    ((midpoint_centralizes_radical hz hzt).trans (centralizer_le hA))
  have hm := cover_moving_index (MovedSection.coverAction (originalMovedSection h) cv.equiv)
    (MovedSection.coverProjection (originalMovedSection h) cv.equiv) cv.cover (U R z) A
    cv.embedding cv.injective cv.range_eq (cv.actor.comp (inclusion hA))
    (fun x w => cv.actor_conjugation (inclusion hA x) w)
  have hFc : Nat.card cv.field.Carrier=2^n := cv.field.card_eq.trans (congrArg (2^·) cv.degree)
  exact he.trans (hm.trans (congrArg (·^_) hFc))

private theorem plane_cover_hyperplane_actor_bound
    (g : Geometry R) (hb : g.b R=2)
    {z t : Vertex R} (hz : color R z=false)
    (hzt : Adjacent R z t)
    (cv : SaturatedDistanceTwo.RadicalPlaneCover R (originalMovedSection h) n z t)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ Q R t)
    (hi : (Z R z ⊓ centralizer (A : Set (FreeAmalgam R))).relIndex
      (Z R z)=2^n) : (Q R z).relIndex A ≤ 2^n := by
  let α := ((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).comp (inclusion hA)
  have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  have hd : Module.finrank cv.field.Carrier (displacementSpace α.range)=1 := by
    have hh := plane_cover_full_fixed_index h hshort hinner g hb hz hzt cv A hA
    have hi' : (centralizer (A : Set (FreeAmalgam R))).relIndex (Z R z)=2^n :=
      (inf_relIndex_left _ _).symm.trans hi
    exact Nat.pow_right_injective hq (hh.symm.trans (hi'.trans (pow_one _).symm))
  have hh := card_actor_le_displacement_dimension α.range
  rw [plane_cover_actor_card h cv A hA,hd,one_pow,pow_one,cv.field.card_eq,cv.degree] at hh
  exact hh

variable (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
  (R.subgroupOf K).map (componentProjection h))
include hnsyl

/-- In the large-image branch the full midpoint is the kernel of both
critical actions, and both images have order q squared. -/
theorem original_source_four_large_midpoint_kernels
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a)) :
    Z R a ⊓ Q R z=Z R t ∧
      Z R z ⊓ Q R a=Z R t ∧
      (Q R z).relIndex (Z R a)=(2^n)^2 ∧
      (Q R a).relIndex (Z R z)=(2^n)^2 := by
  obtain ⟨_,_,hai,hzi,_⟩ := original_source_four_large_paired_geometry h hshort hinner hnsyl g hb path hat hzt hcritical
  have hta := Sp4Four.edge_Z_le_endpoint R path.start_color hat
  have htz := Sp4Four.edge_Z_le_endpoint R path.end_color hzt
  have haQ : Z R a ≤ Q R a :=
    (g.omega_bound a path.start_color (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)).trans (omegaCenter_le _)
  have hzQ : Z R z ≤ Q R z :=
    (g.omega_bound z path.end_color (by rw [g.distance_constant z path.end_color]; change 0 < g.b R; omega)).trans (omegaCenter_le _)
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
    by_contra hn
    have hh := (h.original_small_critical_indices_eq_field rev (by omega)
      (by simpa only [h.field_card] using lt_of_not_ge hn)).2
    rw [hh,h.field_card] at hcritical
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith only [hq,hcritical]
  let := finite_Z R a
  let := finite_Z R z
  have hae := SaturatedDistanceTwo.inf_eq_of_index_bound (Z R t) (Z R a) (Q R z)
    hta (htz.trans hzQ) (hai.trans_le hcritical)
  have hze := SaturatedDistanceTwo.inf_eq_of_index_bound (Z R t) (Z R z) (Q R a)
    htz (hta.trans haQ) (hzi.trans_le hreverse)
  refine ⟨hae,hze,?_,?_⟩
  · rw [←inf_relIndex_left,hae,hai]
  · rw [←inf_relIndex_left,hze,hzi]

/-- The escaping opposite centralizer in the large-image hyperplane
argument has exactly field order modulo its kernel, and fills the entire
hyperplane fixer modulo the full endpoint core. -/
theorem original_source_four_large_escaping_hyperplane
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (P : Subgroup (FreeAmalgam R))
    (hP : P ≤ Q R t)
    (hpoint : P=Q R t ⊓ centralizer
      (Z R z ⊓ centralizer (P : Set (FreeAmalgam R)) : Set (FreeAmalgam R)))
    (hi : (Z R z ⊓ centralizer (P : Set (FreeAmalgam R))).relIndex (Z R z)=2^n)
    (hescape : ¬ Z R a ⊓ centralizer
      (Z R z ⊓ centralizer (P : Set (FreeAmalgam R)) : Set (FreeAmalgam R)) ≤ Q R z) :
    let X := Z R z ⊓ centralizer (P : Set (FreeAmalgam R))
    let Y := Z R a ⊓ centralizer (X : Set (FreeAmalgam R))
    Y.relIndex (Z R a)=2^n ∧ (Q R z).relIndex Y=2^n ∧
      P=Q R z ⊔ Y ∧ ⁅Z R z,P⁆=⁅Z R z,Y⁆ := by
  have ht : color R t = true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSa : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  let X := Z R z ⊓ centralizer (P : Set (FreeAmalgam R))
  let Y := Z R a ⊓ centralizer (X : Set (FreeAmalgam R))
  let C := Z R t
  have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  obtain ⟨⟨ca⟩,⟨cz⟩,hai,hzi,_⟩ := original_source_four_large_paired_geometry h hshort hinner hnsyl g hb path hat hzt hcritical
  obtain ⟨hak,hzk,_,_⟩ := original_source_four_large_midpoint_kernels h hshort hinner hnsyl g hb path hat hzt hcritical
  have hta : C ≤ Z R a := Sp4Four.edge_Z_le_endpoint R path.start_color hat
  have htz : C ≤ Z R z := Sp4Four.edge_Z_le_endpoint R path.end_color hzt
  have haQ : Z R a ≤ Q R a :=
    (g.omega_bound a path.start_color (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)).trans (omegaCenter_le _)
  have hzQ : Z R z ≤ Q R z :=
    (g.omega_bound z path.end_color (by rw [g.distance_constant z path.end_color]; change 0 < g.b R; omega)).trans (omegaCenter_le _)
  have hCT : C ≤ centralizer (Q R t : Set (FreeAmalgam R)) :=
    midpoint_centralizes_radical path.end_color hzt
  have hCX : C ≤ X := le_inf htz (hCT.trans (centralizer_le hP))
  have hCY : C ≤ Y := le_inf hta (hCT.trans (centralizer_le
    (inf_le_left.trans (hzQ.trans hQzT))))
  have hXT : X ≤ Q R t := inf_le_left.trans (hzQ.trans hQzT)
  have hYT : Y ≤ Q R t := inf_le_left.trans (haQ.trans hQaT)
  let := finite_Z R a
  let := finite_Z R z
  let : Finite X := Finite.of_injective (inclusion (show X ≤ Z R z from inf_le_left)) (inclusion_injective _)
  let : Finite Y := Finite.of_injective (inclusion (show Y ≤ Z R a from inf_le_left)) (inclusion_injective _)
  have hXi : C.relIndex X=2^n := by
    have hm := relIndex_mul_relIndex C X (Z R z) hCX inf_le_left
    rw [hi,hzi] at hm
    nlinarith only [hm,hq]
  have hXker : X ⊓ Q R a=C := by
    apply le_antisymm
    · exact (inf_le_inf_right _ (show X ≤ Z R z from inf_le_left)).trans_eq hzk
    · exact le_inf hCX (hta.trans haQ)
  have hYker : Y ⊓ Q R z=C := by
    apply le_antisymm
    · exact (inf_le_inf_right _ (show Y ≤ Z R a from inf_le_left)).trans_eq hak
    · exact le_inf hCY (htz.trans hzQ)
  let αX := ((commutator (Sp ca.field.Carrier)).subtype.comp ca.actor).comp (inclusion hXT)
  have hXcard : Nat.card αX.range=2^n := by
    rw [plane_cover_actor_card h ca X hXT,←inf_relIndex_left,hXker,hXi]
  let r := Module.finrank ca.field.Carrier (displacementSpace αX.range)
  have hr : Y.relIndex (Z R a)=(2^n)^r := by
    rw [inf_relIndex_left]
    exact plane_cover_full_fixed_index h hshort hinner g hb path.start_color hat ca X hXT
  have hr0 : r ≠ 0 := by
    intro he
    have hh := card_actor_le_displacement_dimension αX.range
    rw [hXcard,show Module.finrank ca.field.Carrier (displacementSpace αX.range)=0 from he] at hh
    simp only [zero_pow (by decide : (2:ℕ) ≠ 0),pow_zero] at hh
    omega
  have hCYn : C.relIndex Y ≠ 1 := by
    intro he
    exact hescape ((relIndex_eq_one.mp he).trans (htz.trans hzQ))
  have hCYpos : 0 < C.relIndex Y := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hr1 : r=1 := by
    by_contra hn
    have hr2 : 2 ≤ r := by omega
    have hbnd := Nat.pow_le_pow_right (by omega : 0 < 2^n) hr2
    have hm := relIndex_mul_relIndex C Y (Z R a) hCY inf_le_left
    rw [hai,hr] at hm
    have hk : 2 ≤ C.relIndex Y := by omega
    nlinarith only [hm,hbnd,hk,hq]
  have hYindex : Y.relIndex (Z R a)=2^n := by rw [hr,hr1,pow_one]
  have hYq : (Q R z).relIndex Y=2^n := by
    rw [←inf_relIndex_left,hYker]
    have hm := relIndex_mul_relIndex C Y (Z R a) hCY inf_le_left
    rw [hai,hYindex] at hm
    nlinarith only [hm,hq]
  have hYP : Y ≤ P := by rw [hpoint]; exact le_inf hYT inf_le_right
  have hQP : Q R z ≤ P := by
    rw [hpoint]
    exact le_inf hQzT (le_centralizer_iff.mp (inf_le_left.trans
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R z path.end_color))))
  have hPcard := plane_cover_hyperplane_actor_bound h hshort hinner g hb path.end_color hzt cz P hP hi
  have hQPnorm : Y ≤ normalizer (Q R z : Set (FreeAmalgam R)) :=
    (hYT.trans hTSz).trans (Q_normalized R z)
  have hjoin : P=Q R z ⊔ Y := by
    have hJP : Q R z ⊔ Y ≤ P := sup_le hQP hYP
    have hm := relIndex_mul_relIndex (Q R z) (Q R z ⊔ Y) P le_sup_left hJP
    have hj : (Q R z).relIndex (Q R z ⊔ Y)=(Q R z).relIndex Y := by
      let J := Q R z ⊔ Y
      let : ((Q R z).subgroupOf J).Normal :=
        normal_subgroupOf_of_le_normalizer (sup_le (Q R z).le_normalizer hQPnorm)
      have hh := relIndex_sup_left (Y.subgroupOf J) ((Q R z).subgroupOf J)
      rw [←subgroupOf_sup (show Q R z ≤ J from le_sup_left) (show Y ≤ J from le_sup_right),
        relIndex_subgroupOf (show J ≤ J from le_rfl),relIndex_subgroupOf (show Y ≤ J from le_sup_right)] at hh
      exact hh
    rw [hj,hYq] at hm
    have hn : 0 < (Q R z ⊔ Y).relIndex P := Nat.pos_of_ne_zero
      (mt (relIndex_eq_zero_of_le_left (show Q R z ≤ Q R z ⊔ Y from le_sup_left))
        (by
          have hh := plane_cover_actor_card h cz P hP
          exact hh ▸ (Nat.ne_of_gt Nat.card_pos)))
    have he : (Q R z ⊔ Y).relIndex P=1 := by nlinarith only [hm,hPcard,hn,hq]
    exact le_antisymm (relIndex_eq_one.mp he) hJP
  refine ⟨hYindex,hYq,hjoin,?_⟩
  apply le_antisymm ?_ (commutator_mono le_rfl hYP)
  apply commutator_le_moving_of_inner_mod_centralizer (Z R z) Y P
    ((hYT.trans hTSz).trans (Z_normalized R z))
  rw [hjoin,sup_comm]
  exact sup_le_sup_left (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R z path.end_color))) _

/-- In the escaping-centralizer branch the hyperplane moves the opposite
full cover in a root preimage, including the entire opposite attachment. -/
theorem original_source_four_large_escaping_movement
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (P : Subgroup (FreeAmalgam R))
    (hP : P ≤ Q R t)
    (hpoint : P=Q R t ⊓ centralizer
      (Z R z ⊓ centralizer (P : Set (FreeAmalgam R)) : Set (FreeAmalgam R)))
    (hi : (Z R z ⊓ centralizer (P : Set (FreeAmalgam R))).relIndex (Z R z)=2^n)
    (hescape : ¬ Z R a ⊓ centralizer
      (Z R z ⊓ centralizer (P : Set (FreeAmalgam R)) : Set (FreeAmalgam R)) ≤ Q R z) :
    let X := Z R z ⊓ centralizer (P : Set (FreeAmalgam R))
    let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
    A ≤ ⁅X,Z R a⁆ ∧ A.relIndex ⁅X,Z R a⁆=2^n ∧
      Nat.card (⁅X,Z R a⁆ : Subgroup (FreeAmalgam R))=2^n * Nat.card A := by
  have ht : color R t = true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSa : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  let X := Z R z ⊓ centralizer (P : Set (FreeAmalgam R))
  let Y := Z R a ⊓ centralizer (X : Set (FreeAmalgam R))
  let C := Z R t
  have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  obtain ⟨⟨ca⟩,_,hai,hzi,hmoveA,_,_⟩ := original_source_four_large_paired_geometry h hshort hinner hnsyl g hb path hat hzt hcritical
  obtain ⟨hak,hzk,_,_⟩ := original_source_four_large_midpoint_kernels h hshort hinner hnsyl g hb path hat hzt hcritical
  have hta : C ≤ Z R a := Sp4Four.edge_Z_le_endpoint R path.start_color hat
  have htz : C ≤ Z R z := Sp4Four.edge_Z_le_endpoint R path.end_color hzt
  have haQ : Z R a ≤ Q R a :=
    (g.omega_bound a path.start_color (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)).trans (omegaCenter_le _)
  have hzQ : Z R z ≤ Q R z :=
    (g.omega_bound z path.end_color (by rw [g.distance_constant z path.end_color]; change 0 < g.b R; omega)).trans (omegaCenter_le _)
  have hCT : C ≤ centralizer (Q R t : Set (FreeAmalgam R)) :=
    midpoint_centralizes_radical path.end_color hzt
  have hCX : C ≤ X := le_inf htz (hCT.trans (centralizer_le hP))
  have hCY : C ≤ Y := le_inf hta (hCT.trans (centralizer_le
    (inf_le_left.trans (hzQ.trans hQzT))))
  have hXT : X ≤ Q R t := inf_le_left.trans (hzQ.trans hQzT)
  have hYT : Y ≤ Q R t := inf_le_left.trans (haQ.trans hQaT)
  let := finite_Z R a
  let := finite_Z R z
  let : Finite X := Finite.of_injective (inclusion (show X ≤ Z R z from inf_le_left)) (inclusion_injective _)
  let : Finite Y := Finite.of_injective (inclusion (show Y ≤ Z R a from inf_le_left)) (inclusion_injective _)
  have hXi : C.relIndex X=2^n := by
    have hm := relIndex_mul_relIndex C X (Z R z) hCX inf_le_left
    rw [hi,hzi] at hm
    nlinarith only [hm,hq]
  have hXker : X ⊓ Q R a=C := by
    apply le_antisymm
    · exact (inf_le_inf_right _ (show X ≤ Z R z from inf_le_left)).trans_eq hzk
    · exact le_inf hCX (hta.trans haQ)
  have hYker : Y ⊓ Q R z=C := by
    apply le_antisymm
    · exact (inf_le_inf_right _ (show Y ≤ Z R a from inf_le_left)).trans_eq hak
    · exact le_inf hCY (htz.trans hzQ)
  let αX := ((commutator (Sp ca.field.Carrier)).subtype.comp ca.actor).comp (inclusion hXT)
  have hXcard : Nat.card αX.range=2^n := by
    rw [plane_cover_actor_card h ca X hXT,←inf_relIndex_left,hXker,hXi]
  let r := Module.finrank ca.field.Carrier (displacementSpace αX.range)
  have hr : Y.relIndex (Z R a)=(2^n)^r := by
    rw [inf_relIndex_left]
    exact plane_cover_full_fixed_index h hshort hinner g hb path.start_color hat ca X hXT
  have hYindex := (original_source_four_large_escaping_hyperplane h hshort hinner hnsyl g hb path hat hzt
    hcritical P hP hpoint hi hescape).1
  have hr1 : r=1 := Nat.pow_right_injective hq
    (hr.symm.trans (hYindex.trans (pow_one _).symm))
  have hFa : Nat.card ca.field.Carrier=2^n := ca.field.card_eq.trans (congrArg (2^·) ca.degree)
  have hlarge : 2 < Nat.card ca.field.Carrier := by
    rw [hFa]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.nonbinary
  let s := originalMovedSection h
  let p := MovedSection.coverProjection s ca.equiv
  let σ := MovedSection.coverAction s ca.equiv
  let β := ca.actor.comp (inclusion hXT)
  have hβact (x : X) (w : s.space.toSubmodule) :
      ca.embedding (Multiplicative.ofAdd (σ (β x) w))=
        x.val*ca.embedding (Multiplicative.ofAdd w)*x.val⁻¹ := ca.actor_conjugation (inclusion hXT x) w
  have hR : ⁅Z R a,Z R z⁆ ≤ C := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl haQ).trans
      (original_source_two_midpoint_containment h hshort hinner g hb hnsyl path hat hzt)
  have hcomm : ⁅X,U R a⁆ ≤ centralizer (X : Set (FreeAmalgam R)) := by
    rw [commutator_comm]
    exact ((commutator_mono (U_le_Z a) hXT).trans_eq hmoveA).trans
      (hR.trans (hCT.trans (centralizer_le hXT)))
  have hquad := embedded_actor_quadratic p ca.cover (U R a) X
    ca.embedding ca.injective ca.range_eq β hβact hcomm
  have hk : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map ca.embedding=
      U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) := by
    apply le_antisymm
    · rintro x ⟨w,hw,rfl⟩
      exact ⟨ca.range_eq ▸ ⟨w,rfl⟩,(ca.kernel _).mp hw⟩
    · rintro x ⟨hx,hc⟩
      obtain ⟨w,rfl⟩ := ca.range_eq.symm ▸ hx
      exact ⟨w,(ca.kernel _).mpr hc,rfl⟩
  obtain ⟨hkerle,hkerindex⟩ := embedded_root_displacement_index
    (U R a) X ((hXT.trans hTSa).trans (U_normalized a))
    σ p ca.cover ca.embedding ca.injective ca.range_eq β hβact hlarge (hXcard.trans hFa.symm) hr1 hquad
  change p.toLinearMap.ker.toAddSubgroup.toSubgroup.map ca.embedding ≤ ⁅X,U R a⁆ at hkerle
  change (p.toLinearMap.ker.toAddSubgroup.toSubgroup.map ca.embedding).relIndex ⁅X,U R a⁆=Nat.card ca.field.Carrier at hkerindex
  rw [hk] at hkerle hkerindex
  rw [hFa] at hkerindex
  let := g.Z_elementary (by omega : 0 < g.b R) a path.start_color
  have hCU : C ≤ normalizer (U R a : Set (FreeAmalgam R)) :=
    (hta.trans ((Z R a).le_centralizer.trans (centralizer_le (U_le_Z a)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hmove : ⁅X,Z R a⁆=⁅X,U R a⁆ := by
    rw [original_Z_eq_moving_sup_edge h hshort hinner g hb path.start_color hat]
    exact movement_central_supplement (U R a) C (Q R t) X hCU hCT hXT
  rw [←hmove] at hkerle hkerindex
  have hcard : Nat.card (⁅X,Z R a⁆ : Subgroup (FreeAmalgam R))=
      2^n * Nat.card (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) : Subgroup (FreeAmalgam R)) := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R))
      (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)))
      ⁅X,Z R a⁆ bot_le hkerle
    simpa only [relIndex_bot_left,hkerindex,mul_comm] using hh.symm
  exact ⟨hkerle,hkerindex,hcard⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
