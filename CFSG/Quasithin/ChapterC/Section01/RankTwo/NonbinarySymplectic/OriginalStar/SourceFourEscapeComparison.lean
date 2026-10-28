module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourEscape
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourEscape
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourEscapeComparison

/-!
# Comparing escaping hyperplane attachments in the original radical

For the original large critical image, both complete fixed attachments have
identical order through the same moved-section kernel. An escaping opposite
centralizer cannot have its movement contained in the hyperplane displacement
when the attachments differ. Below field order, the natural image of the
hyperplane movement has field-power order, which forces containment of the
other attachment. Individual commutators then identify both attachments.
Thus unequal attachments in this escape case must both have full field order.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(4), printed p.875.
Generic cover calculations are reused internally; the applications use the
original radical, its odd-index witness, and both entire fixed attachments.
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

/-- Below the maximal covering-kernel order, every element of the escaping
hyperplane movement outside that kernel is an individual commutator of the
actual hyperplane and the opposite original moving module. -/
theorem original_source_four_large_escaping_value
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
      (Z R z ⊓ centralizer (P : Set (FreeAmalgam R)) : Set (FreeAmalgam R)) ≤ Q R z)
    (hsmall : Nat.card (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) :
      Subgroup (FreeAmalgam R)) ≠ 2^n)
    (x : FreeAmalgam R)
    (hx : x ∈ ⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),Z R a⁆)
    (hn : x ∉ U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))) :
    ∃ b ∈ Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),
      ∃ u ∈ U R a, ⁅b,u⁆=x := by
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  let X := Z R z ⊓ centralizer (P : Set (FreeAmalgam R))
  let Y := Z R a ⊓ centralizer (X : Set (FreeAmalgam R))
  let C := Z R t
  have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  have geom := original_source_four_large_paired_geometry h hshort hinner hnsyl g hb path hat hzt hcritical
  let ca := Classical.choice geom.1
  have hzi := geom.2.2.2.1
  have hmoveA := geom.2.2.2.2.1
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
  have hXT : X ≤ Q R t := inf_le_left.trans (hzQ.trans (Q_le_adjacent_h R ht hzt))
  let := finite_Z R a
  let := finite_Z R z
  let : Finite X := Finite.of_injective (inclusion (show X ≤ Z R z from inf_le_left)) (inclusion_injective _)
  have hXi : C.relIndex X=2^n := by
    have hm := relIndex_mul_relIndex C X (Z R z) hCX inf_le_left
    rw [hi,hzi] at hm
    nlinarith only [hm,hq]
  have hXker : X ⊓ Q R a=C := by
    apply le_antisymm
    · exact (inf_le_inf_right _ (show X ≤ Z R z from inf_le_left)).trans_eq hzk
    · exact le_inf hCX (hta.trans haQ)
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
  have hR : ⁅Z R a,Z R z⁆ ≤ C := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl haQ).trans
      (original_source_two_midpoint_containment h hshort hinner g hb hnsyl path hat hzt)
  have hcomm : ⁅X,U R a⁆ ≤ centralizer (X : Set (FreeAmalgam R)) := by
    rw [commutator_comm]
    exact ((commutator_mono (U_le_Z a) hXT).trans_eq hmoveA).trans
      (hR.trans (hCT.trans (centralizer_le hXT)))
  let := g.Z_elementary (by omega : 0 < g.b R) a path.start_color
  have hCU : C ≤ normalizer (U R a : Set (FreeAmalgam R)) :=
    (hta.trans ((Z R a).le_centralizer.trans (centralizer_le (U_le_Z a)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hmove : ⁅X,Z R a⁆=⁅X,U R a⁆ := by
    rw [original_Z_eq_moving_sup_edge h hshort hinner g hb path.start_color hat]
    exact movement_central_supplement (U R a) C (Q R t) X hCU hCT hXT
  exact SaturatedDistanceTwo.plane_cover_value ca X hXT hXcard hr1 hcomm
    (Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.nonbinary) hsmall x (hmove ▸ hx) hn

omit hnsyl in
/-- An individual commutator of the two full Z-layers cannot be a nonidentity
member of either endpoint's complete fixed attachment. The midpoint supplement
is retained and centralizes the other full Z-layer. -/
theorem original_critical_full_value_in_fixed_eq_one
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R=2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (b : FreeAmalgam R) (hbZ : b ∈ Z R z)
    (u : FreeAmalgam R) (hu : u ∈ Z R a)
    (hfix : ⁅b,u⁆ ∈ centralizer (Ltilde R a : Set (FreeAmalgam R))) :
    ⁅b,u⁆=1 := by
  let := g.Z_elementary (by omega : 0 < g.b R) a path.start_color
  let := g.Z_elementary (by omega : 0 < g.b R) z path.end_color
  have hta := Sp4Four.edge_Z_le_endpoint R path.start_color hat
  have htz := Sp4Four.edge_Z_le_endpoint R path.end_color hzt
  have hn : Z R t ≤ normalizer (U R a : Set (FreeAmalgam R)) :=
    (hta.trans ((Z R a).le_centralizer.trans (centralizer_le (U_le_Z a)))).trans
      (Subgroup.centralizer_le_normalizer _)
  rw [original_Z_eq_moving_sup_edge h hshort hinner g hb path.start_color hat,
    ←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hn] at hu
  obtain ⟨v,hv,w,hw,rfl⟩ := hu
  have hbw : Commute b w := (Z R z).le_centralizer (htz hw) b hbZ
  have he : ⁅b,v*w⁆=⁅b,v⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj,commutatorElement_eq_one_iff_commute.mpr hbw]
    simp only [mul_one,mul_inv_cancel_right]
  rw [he] at hfix ⊢
  exact original_critical_value_in_fixed_eq_one h hinner path hb hat b hbZ v hv hfix


/-- In the large branch the full attachments have equal orders, because
both are images of the kernel of the original moved-section quotient. -/
theorem original_source_four_large_attachment_card_eq
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a)) :
    Nat.card (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) :
      Subgroup (FreeAmalgam R)) =
    Nat.card (U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) :
      Subgroup (FreeAmalgam R)) := by
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  have geom := original_source_four_large_paired_geometry h hshort hinner hnsyl g hb path hat hzt hcritical
  exact (SaturatedDistanceTwo.plane_attachment_card (Classical.choice geom.1)).trans
    (SaturatedDistanceTwo.plane_attachment_card (Classical.choice geom.2.1)).symm

/-- If the opposite hyperplane centralizer escapes, containment of its
movement in the first hyperplane movement would force both full attachments
trivial. Thus unequal attachments exclude that containment, as on p.875. -/
theorem original_source_four_large_escaping_not_le_hyperplane
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (P B : Subgroup (FreeAmalgam R)) (hP : P ≤ Q R t)
    (hpoint : P=Q R t ⊓ centralizer
      (Z R z ⊓ centralizer (P : Set (FreeAmalgam R)) : Set (FreeAmalgam R)))
    (hi : (Z R z ⊓ centralizer (P : Set (FreeAmalgam R))).relIndex (Z R z)=2^n)
    (hB : ∀ b : FreeAmalgam R, b ∈ B ↔ b ∈ Q R t ∧
      ∀ x ∈ Z R z ⊓ centralizer (P : Set (FreeAmalgam R)), ⁅b,x⁆ ∈ ⁅Z R z,P⁆)
    (hcard : Nat.card (⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),B⁆ :
      Subgroup (FreeAmalgam R))=2^n)
    (hne : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) ≠
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)))
    (hescape : ¬ Z R a ⊓ centralizer
      (Z R z ⊓ centralizer (P : Set (FreeAmalgam R)) : Set (FreeAmalgam R)) ≤ Q R z) :
    ¬ ⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),Z R a⁆ ≤
      ⁅Z R z,P⁆ := by
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  let X := Z R z ⊓ centralizer (P : Set (FreeAmalgam R))
  let M := ⁅X,Z R a⁆
  let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
  let A' := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
  intro hle
  have hZaT : Z R a ≤ Q R t :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)).trans
      ((omegaCenter_le _).trans (Q_le_adjacent_h R ht hat))
  have hZaB : Z R a ≤ B := by
    intro b hbZ
    refine (hB b).mpr ⟨hZaT hbZ,fun x hx => ?_⟩
    apply hle
    rw [commutator_comm X]
    exact commutator_mem_commutator hbZ hx
  have hMD : M ≤ ⁅X,B⁆ := commutator_mono le_rfl hZaB
  let : Finite (⁅X,B⁆ : Subgroup (FreeAmalgam R)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hMc := Nat.card_le_card_of_injective (inclusion hMD) (inclusion_injective _)
  rw [hcard] at hMc
  have hcm := (original_source_four_large_escaping_movement h hshort hinner hnsyl g hb path hat hzt
    hcritical P hP hpoint hi hescape).2.2
  have hAc : Nat.card A ≤ 1 := by
    change Nat.card M=2^n*Nat.card A at hcm
    have hq : 0 < 2^n := by positivity
    nlinarith only [hMc,hcm,hq]
  let := finite_Z R a
  let : Finite A := Finite.of_injective (inclusion (inf_le_left.trans (U_le_Z a))) (inclusion_injective _)
  have hA : A=⊥ := A.eq_bot_of_card_le hAc
  have hc := original_source_four_large_attachment_card_eq h hshort hinner hnsyl g hb path hat hzt hcritical
  change Nat.card A=Nat.card A' at hc
  have hA' : A'=⊥ := Subgroup.card_eq_one.mp (hc.symm.trans (hA ▸ Subgroup.card_bot))
  exact hne (hA.trans hA'.symm)

/-- Below full field order, the intersection of the escaping root movement
with the opposite attachment is exactly the intersection of the two attachments.
This is the individual-commutator comparison in source (4), before the remaining
geometric containment of that attachment has been established. -/
theorem original_source_four_large_escaping_attachment_intersection
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
    (hsmall : Nat.card (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) :
      Subgroup (FreeAmalgam R)) ≠ 2^n) :
    let X := Z R z ⊓ centralizer (P : Set (FreeAmalgam R))
    let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
    let A' := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
    ⁅X,Z R a⁆ ⊓ A'=A ⊓ A' := by
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  let X := Z R z ⊓ centralizer (P : Set (FreeAmalgam R))
  let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
  let A' := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  apply le_antisymm
  · rintro x ⟨hx,hxA'⟩
    refine ⟨?_,hxA'⟩
    by_contra hn
    obtain ⟨b,hbX,u,hu,he⟩ := original_source_four_large_escaping_value h hshort hinner hnsyl g hb path hat hzt
      hcritical P hP hpoint hi hescape hsmall x hx hn
    have hc : ⁅u,b⁆ ∈ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
      rw [←commutatorElement_inv,he]
      exact inv_mem hxA'.2
    have he1 := original_critical_full_value_in_fixed_eq_one h hshort hinner rev hb hzt hat
      u (U_le_Z a hu) b hbX.1 hc
    have he2 : ⁅b,u⁆=1 := commutatorElement_eq_one_iff_commute.mpr
      (commutatorElement_eq_one_iff_commute.mp he1).symm
    exact hn (he.symm ▸ he2.symm ▸ A.one_mem)
  · exact inf_le_inf_right _
      (original_source_four_large_escaping_movement h hshort hinner hnsyl g hb path hat hzt
        hcritical P hP hpoint hi hescape).1
/-- The movement of a full fixed hyperplane has field-power index over
its intersection with the entire attachment. This retains the binary cover
kernel and uses the actual common-radical actions at the first endpoint. -/
theorem original_source_four_large_hyperplane_movement_index
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (P : Subgroup (FreeAmalgam R)) (hP : P ≤ Q R t) :
    ∃ r : ℕ, (U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))).relIndex
      ⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),Z R a⁆ = (2^n)^r := by
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  have geom := original_source_four_large_paired_geometry h hshort hinner hnsyl g hb path hat hzt hcritical
  let cv := Classical.choice geom.2.1
  let C := Z R t
  let X₀ := U R z ⊓ centralizer (P : Set (FreeAmalgam R))
  have hZaT : Z R a ≤ Q R t :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)).trans
      ((omegaCenter_le _).trans (Q_le_adjacent_h R ht hat))
  have hCT : C ≤ centralizer (Q R t : Set (FreeAmalgam R)) :=
    midpoint_centralizes_radical path.end_color hzt
  have hCZ : C ≤ Z R z := Sp4Four.edge_Z_le_endpoint R path.end_color hzt
  let := g.Z_elementary (by omega : 0 < g.b R) z path.end_color
  have hCU : C ≤ normalizer (U R z : Set (FreeAmalgam R)) :=
    (hCZ.trans ((Z R z).le_centralizer.trans (centralizer_le (U_le_Z z)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCX : C ≤ normalizer (X₀ : Set (FreeAmalgam R)) :=
    (hCZ.trans ((Z R z).le_centralizer.trans (centralizer_le
      (inf_le_left.trans (U_le_Z z))))).trans (Subgroup.centralizer_le_normalizer _)
  have hX : Z R z ⊓ centralizer (P : Set (FreeAmalgam R))=X₀ ⊔ C := by
    rw [original_Z_eq_moving_sup_edge h hshort hinner g hb path.end_color hzt,
      sup_comm (U R z),inf_centralizer_sup_of_centralizing C (U R z) P
        hCU (hCT.trans (centralizer_le hP)),sup_comm]
  have he : ⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),Z R a⁆=
      ⁅Z R a,X₀⁆ := by
    rw [commutator_comm,hX]
    exact movement_central_supplement X₀ C (Q R t) (Z R a) hCX hCT hZaT
  obtain ⟨r,hr⟩ := SaturatedDistanceTwo.plane_cover_fixed_movement_index cv (Z R a) P hZaT hP
  rw [he]
  exact ⟨r,hr⟩
/-- The escaping-centralizer subcase of source (4) cannot have unequal
attachments of less than field order. The first attachment lies in the
opposite movement by its field-power index; individual commutators then
identify the two complete attachments. -/
theorem original_source_four_large_escaping_small_attachment_eq
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
    (hsmall : Nat.card (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) :
      Subgroup (FreeAmalgam R)) ≠ 2^n) :
    U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) =
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  let X := Z R z ⊓ centralizer (P : Set (FreeAmalgam R))
  let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
  let A' := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
  let M := ⁅X,Z R a⁆
  let := finite_Z R a
  let := finite_Z R z
  let : Finite A := Finite.of_injective (inclusion (inf_le_left.trans (U_le_Z a))) (inclusion_injective _)
  let : Finite A' := Finite.of_injective (inclusion (inf_le_left.trans (U_le_Z z))) (inclusion_injective _)
  have hcards : Nat.card A=Nat.card A' :=
    original_source_four_large_attachment_card_eq h hshort hinner hnsyl g hb path hat hzt hcritical
  have hMcard : Nat.card M=2^n*Nat.card A' :=
    (original_source_four_large_escaping_movement h hshort hinner hnsyl g hb path hat hzt
      hcritical P hP hpoint hi hescape).2.2.trans (congrArg (2^n*·) hcards)
  let : Finite M := Nat.finite_of_card_ne_zero (by rw [hMcard]; exact mul_ne_zero (by positivity) Nat.card_pos.ne')
  have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  have hsmall' : Nat.card A' < 2^n := by
    have hh := original_moving_fixed_attachment_card_le_field h path.start_color
    change Nat.card A ≤ 2^n at hh
    rw [←hcards]
    exact lt_of_le_of_ne hh hsmall
  obtain ⟨r,hr⟩ := original_source_four_large_hyperplane_movement_index h hshort hinner hnsyl g hb path hat hzt hcritical P hP
  have hA'M : A' ≤ M := SaturatedDistanceTwo.attachment_le_of_field_power_index A' M hq hsmall' hMcard r hr
  have hmeet : M ⊓ A'=A ⊓ A' := original_source_four_large_escaping_attachment_intersection
    h hshort hinner hnsyl g hb path hat hzt hcritical P hP hpoint hi hescape hsmall
  have hA'A : A' ≤ A := by
    have he : A'=A ⊓ A' := (inf_eq_right.mpr hA'M).symm.trans hmeet
    exact he.le.trans inf_le_left
  exact (Subgroup.eq_of_le_of_card_ge hA'A hcards.le).symm


/-- The actual hyperplane supplied by source (4), with the escaping movement
excluded from H when the full attachments differ. In that escaping subcase
both complete attachments must have field order. All section centralizers are literal. -/
theorem original_source_four_large_unequal_hyperplane
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
        Nat.card A₁=2^n ∧ Nat.card A₀=2^n) := by
  obtain ⟨P,B,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR⟩ :=
    original_source_four_large_hyperplane_attachment h hshort hinner hnsyl g hb path hat hzt hcritical
  refine ⟨P,B,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,?_⟩
  intro hescape
  have hfull : Nat.card (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) :
      Subgroup (FreeAmalgam R))=2^n := by
    by_contra hn
    exact hne (original_source_four_large_escaping_small_attachment_eq h hshort hinner hnsyl g hb path hat hzt
      hcritical P hP hpoint hi hescape hn)
  exact ⟨original_source_four_large_escaping_not_le_hyperplane h hshort hinner hnsyl g hb path hat hzt
    hcritical P B hP hpoint hi hmem hcard hne hescape,hfull,
    (original_source_four_large_attachment_card_eq h hshort hinner hnsyl g hb path hat hzt hcritical).symm.trans hfull⟩


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
