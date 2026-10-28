module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourEscapeComparison
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourEscape
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourFullIntersection

/-!
# Full-size movement intersections in the original radical

At full attachment order, the universal orthogonal cover maps bijectively
onto the original moving group. Fixed spaces and movements inherit its
field structure. The intersection of the two escaping hyperplane movements
therefore has field-power order. Both movements have order q squared and
lie in a common fixed layer of order q cubed; they are distinct, so their
intersection has exactly order q. The original quotient actions and both
full attachments are retained throughout.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(4), printed p.875.
The internal import reuses only generic full-cover and subgroup-product
calculations, applied here to the original plane cover.
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
private theorem full_plane_fixed_movement_intersection
    {a t : Vertex R}
    (cv : SaturatedDistanceTwo.RadicalPlaneCover R (originalMovedSection h) n a t)
    (hfull : Nat.card (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) :
      Subgroup (FreeAmalgam R))=2^n)
    (X Z : Subgroup (FreeAmalgam R)) (hX : X ≤ Q R t) (hZ : Z ≤ Q R t) :
    Nat.card (U R a)=(2^n)^5 ∧ ∃ r : ℕ,
      Nat.card (⁅X,U R a⁆ ⊓ ⁅Z,U R a ⊓ centralizer (X : Set (FreeAmalgam R))⁆ :
        Subgroup (FreeAmalgam R))=(2^n)^r := by
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
  simpa only [hFc] using full_cover_fixed_movement_intersection p cv.cover hc
    cv.embedding cv.injective (U R a) X Z cv.range_eq
    (cv.actor.comp (inclusion hX)) (cv.actor.comp (inclusion hZ))
    (fun x w => cv.actor_conjugation (inclusion hX x) w)
    (fun z w => cv.actor_conjugation (inclusion hZ z) w)

/-- The full-size escape intersection has field-power order. The proof realizes
both movements as field subspaces while retaining the original full cover. -/
theorem original_source_four_large_full_intersection_power
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
      Subgroup (FreeAmalgam R))=2^n) :
    Nat.card (U R a)=(2^n)^5 ∧ ∃ r : ℕ,
      Nat.card (⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),Z R a⁆ ⊓
        ⁅Z R z,P⁆ : Subgroup (FreeAmalgam R))=(2^n)^r := by
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
  have hZT := hzQ.trans (Q_le_adjacent_h R ht hzt)
  have hXT : X ≤ Q R t := inf_le_left.trans hZT
  have hCT : C ≤ centralizer (Q R t : Set (FreeAmalgam R)) :=
    midpoint_centralizes_radical path.end_color hzt
  have hCA : C ≤ Z R a := Sp4Four.edge_Z_le_endpoint R path.start_color hat
  let := g.Z_elementary (by omega : 0 < g.b R) a path.start_color
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
  obtain ⟨hU,r,hr⟩ := full_plane_fixed_movement_intersection h cv hfull X (Z R z) hXT hZT
  exact ⟨hU,r,by rw [hM,hH]; exact hr⟩

private theorem escaping_full_intersection_card
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
    (hMnot : ¬ ⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),Z R a⁆ ≤ ⁅Z R z,P⁆) :
    Nat.card (⁅Z R z ⊓ centralizer (P : Set (FreeAmalgam R)),Z R a⁆ ⊓
      ⁅Z R z,P⁆ : Subgroup (FreeAmalgam R))=2^n := by
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  let X := Z R z ⊓ centralizer (P : Set (FreeAmalgam R))
  let M := ⁅X,Z R a⁆
  let N := ⁅Z R z,P⁆
  let D := U R a ⊓ centralizer (Q R t : Set (FreeAmalgam R))
  let C := Z R t
  let q := 2^n
  have hq : 1 < q := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  obtain ⟨hU,r,hr⟩ := original_source_four_large_full_intersection_power h hshort hinner hnsyl g hb path hat hzt
    hcritical P hP hpoint hi hescape hfull
  have hMcard : Nat.card M=q^2 := by
    have hh := (original_source_four_large_escaping_movement h hshort hinner hnsyl g hb path hat hzt
      hcritical P hP hpoint hi hescape).2.2
    simpa only [hfull,pow_two] using hh
  have geom := original_source_four_large_paired_geometry h hshort hinner hnsyl g hb path hat hzt hcritical
  have haQ : Z R a ≤ Q R a :=
    (g.omega_bound a path.start_color (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)).trans (omegaCenter_le _)
  have hRcent : ⁅Z R a,Z R z⁆ ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
    rw [commutator_comm]
    exact ((commutator_mono le_rfl haQ).trans
      (original_source_two_midpoint_containment h hshort hinner g hb hnsyl path hat hzt)).trans
        (midpoint_centralizes_radical path.start_color hat)
  let := g.Z_elementary (by omega : 0 < g.b R) a path.start_color
  let := finite_Z R a
  let : Finite (U R a) := Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  have hCU : C ≤ normalizer (U R a : Set (FreeAmalgam R)) :=
    ((Sp4Four.edge_Z_le_endpoint R path.start_color hat).trans
      ((Z R a).le_centralizer.trans (centralizer_le (U_le_Z a)))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hRmoving : ⁅Z R a,Z R z⁆=⁅Q R t,U R a⁆ := by
    rw [←geom.2.2.2.2.1,commutator_comm,
      original_Z_eq_moving_sup_edge h hshort hinner g hb path.start_color hat]
    exact movement_central_supplement (U R a) C (Q R t) (Q R t)
      hCU (midpoint_centralizes_radical path.start_color hat) le_rfl
  have hRD : ⁅Z R a,Z R z⁆ ≤ D := le_inf (by
    rw [hRmoving]
    exact le_normalizer_iff_commutator_le_right.mp ((show Q R t ≤ stabilizer R a from fun _ hx => hx.2 _ (adjacent_symm R hat)).trans (U_normalized a))) hRcent
  have hMD : M ≤ D := by
    apply le_trans (show M ≤ ⁅Z R a,Z R z⁆ from ?_) hRD
    exact (commutator_mono (show X ≤ Z R z from inf_le_left) le_rfl).trans_eq
      (commutator_comm (Z R z) (Z R a))
  have hND : N ≤ D := by
    dsimp only [N]
    rw [(original_source_four_large_escaping_hyperplane h hshort hinner hnsyl g hb path hat hzt
      hcritical P hP hpoint hi hescape).2.2.2,commutator_comm]
    exact (commutator_mono inf_le_left le_rfl).trans hRD
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  have hreverse : q^2 ≤ (Q R a).relIndex (Z R z) := by
    rw [(original_source_four_large_midpoint_kernels h hshort hinner hnsyl g hb path hat hzt hcritical).2.2.2]
  have hindex : D.relIndex (U R a)=q^2 := by
    rw [inf_relIndex_left]
    exact (original_source_four_large_plane_cover h hshort hinner hnsyl g hb rev hzt hat hreverse).2.2.1
  have hDcard : Nat.card D=q^3 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R)) D (U R a) bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,hindex,hU] at hh
    apply Nat.eq_of_mul_eq_mul_right (by positivity : 0 < q^2)
    calc
      Nat.card D*q^2 = q^5 := hh
      _ = q^3*q^2 := by ring
  let : Finite D := Finite.of_injective (inclusion (show D ≤ U R a from inf_le_left)) (inclusion_injective _)
  let : Finite M := Finite.of_injective (inclusion hMD) (inclusion_injective _)
  let : Finite N := Finite.of_injective (inclusion hND) (inclusion_injective _)
  let : Finite (M ⊓ N : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion (show M ⊓ N ≤ M from inf_le_left)) (inclusion_injective _)
  have hbound : Nat.card (M ⊓ N : Subgroup (FreeAmalgam R)) < q^2 := by
    have hh := Nat.card_le_card_of_injective (inclusion (show M ⊓ N ≤ M from inf_le_left)) (inclusion_injective _)
    rw [hMcard] at hh
    apply lt_of_le_of_ne hh
    intro he
    have heq : M ⊓ N=M := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [he,hMcard])
    exact hMnot (heq.ge.trans inf_le_right)
  have hrle : r ≤ 1 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by omega : 0 < q) (by omega : 2 ≤ r)
    change Nat.card (M ⊓ N : Subgroup (FreeAmalgam R))=q^r at hr
    omega
  have hnorm : N ≤ normalizer (M : Set (FreeAmalgam R)) :=
    (hND.trans inf_le_left |>.trans (U_le_Z a)).trans
      ((Z R a).le_centralizer.trans (centralizer_le
        (hMD.trans inf_le_left |>.trans (U_le_Z a)))) |>.trans (Subgroup.centralizer_le_normalizer _)
  have hprod := SaturatedDistanceTwo.subgroup_product_card M N hnorm
  have hsup : Nat.card (M ⊔ N : Subgroup (FreeAmalgam R)) ≤ q^3 := by
    have hh := Nat.card_le_card_of_injective (inclusion (sup_le hMD hND)) (inclusion_injective _)
    rwa [hDcard] at hh
  have hrpos : r ≠ 0 := by
    intro he
    change Nat.card (M ⊓ N : Subgroup (FreeAmalgam R))=q^r at hr
    rw [he,pow_zero] at hr
    rw [hMcard,hHcard,hr,one_mul] at hprod
    have hbig : q^3 < q^2*q^2 := by
      calc
        q^3 < q^4 := Nat.pow_lt_pow_right hq (by decide)
        _ = q^2*q^2 := by ring
    exact hbig.not_ge (hprod.trans_le hsup)
  have he : r=1 := by omega
  simpa only [he,pow_one] using hr

/-- The actual hyperplane of source (4) has a field-sized movement intersection
in the unequal-attachment escape case. Its full section-centralizer complement
and both full attachments are retained. -/
theorem original_source_four_large_unequal_intersection
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
        Nat.card (⁅X,Z R a⁆ ⊓ H₀ : Subgroup (FreeAmalgam R))=2^n) := by
  obtain ⟨P,B,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,hesc⟩ :=
    original_source_four_large_unequal_hyperplane h hshort hinner hnsyl g hb path hat hzt hcritical hne
  refine ⟨P,B,hQ,hP,hB,hpoint,hi,hCX,hRX,hmem,hdis,hcard,hjoin,hR,?_⟩
  intro hescape
  obtain ⟨hn,hfull,hfull'⟩ := hesc hescape
  refine ⟨hn,hfull,hfull',?_⟩
  apply escaping_full_intersection_card h hshort hinner hnsyl g hb path hat hzt hcritical
    P hP hpoint hi hescape hfull ?_ hn
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
