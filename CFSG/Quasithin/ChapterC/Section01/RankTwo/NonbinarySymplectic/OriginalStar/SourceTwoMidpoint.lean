module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoPointDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoIndexContradiction
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoFixedCoreIndex
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoIndexContradiction

/-!
# Original-star fixed-core contradiction and midpoint containment

We finish the large-movement comparison for the original nonsylow source
star. Its full point-radical action makes the quadratic fixed-core image
have order q. Both full-radical product bounds are attained. The complete
opposite fixed core gives [D : D ∩ D′] ≤ q⁴, while the order-q fixed
attachment gives [T : T₀D′] ≤ q⁴.

Fixed-vector lifting through the same full natural cover supplies the
reverse index inequalities. Equality forces the order-q² displacement
[Z′,D] into D ∩ T₀D′. Since it is disjoint from D′, the resulting index
is at least q⁵, contradicting q⁴. Thus large movement is impossible.
In the remaining small-movement case, the full quadratic action and the
original T₀ triple imply [Z′,Q] ≤ Z_t.

The final application is to the selected original marked star, with its
own distance-two graph. Its shortness, innerness, original quotient
marking and restricted odd-index witness are supplied by the existing
source-star construction. No marked-image preservation or saturation of
the minimum replacement is assumed. The source critical-index alternative,
subsequent paired-attachment comparison, minimum marked preservation and
saturation, original Sylow branch, n = 2 and block assembly remain.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the midpoint-containment clause of (3.7)(2), printed pp.873--874.
The generic fixed-preimage and relative-index arguments are reused from
the saturated source branch, with all original-graph premises proved here.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Matrix Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

private theorem index_le_product_of_component_le
    {G : Type*} [Group G] (T B D J : Subgroup G) [Finite T]
    (_hBT : B ≤ T) (hDT : D ≤ T) (hJT : J ≤ T) (hBJ : B ≤ J)
    (hJn : T ≤ normalizer (J : Set G)) :
    J.relIndex T ≤ (B ⊔ D).relIndex T * J.relIndex D := by
  have hsup : J.relIndex (J ⊔ D) = J.relIndex D := by
    rw [sup_comm]
    exact relative_sup_index T D J hDT hJT hJn
  have hi := relIndex_mul_relIndex J (J ⊔ D) T le_sup_left (sup_le hJT hDT)
  rw [hsup] at hi
  have hle : (J ⊔ D).relIndex T ≤ (B ⊔ D).relIndex T :=
    relIndex_le_of_le_left (sup_le (hBJ.trans le_sup_left) le_sup_right) index_ne_zero_of_finite
  calc
    _ = J.relIndex D * (J ⊔ D).relIndex T := hi.symm
    _ ≤ J.relIndex D * (B ⊔ D).relIndex T := Nat.mul_le_mul_left _ hle
    _ = _ := Nat.mul_comm _ _

namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open DistanceTwoRecognition ChapterB.QuasisimpleSource MSCentralOrbit
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
include h hshort hinner

omit h hshort hinner [Finite H] [Field F] [Finite F] [CharP F 2] in
private theorem original_componentRadical_normalized
    {a t : Vertex R} (hat : Adjacent R a t) :
    Q R t ≤ normalizer ((Q R t ⊓ Ltilde R a) : Set (FreeAmalgam R)) := by
  have hTS : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  exact (le_inf (Q R t).le_normalizer (hTS.trans (original_residual_normalized a))).trans
    inf_normalizer_le_normalizer_inf

theorem original_source_two_large_fixedCore_actor_index_le_field
    (g : Geometry R) (hb : g.b R = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z)) :
    (Q R z).relIndex (fixedCore R a) ≤ 2^n := by
  have ht : color R t = true := by
    cases he : color R t with
    | false => exact (adjacent_color_ne R hat (path.start_color.trans he.symm)).elim
    | true => rfl
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSa : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  let := h.component_normal
  let s := originalMovedSection h
  obtain ⟨pc⟩ := original_source_two_large_radical_point_cover h hinner g hb hnsyl path hat hzt hlarge
  let E := pc.field
  let α := (commutator (Sp E.Carrier)).subtype.comp pc.actor
  have hDT : fixedCore R a ≤ Q R t := inf_le_left.trans hQaT
  let β := pc.actor.comp (inclusion hDT)
  let δ := (commutator (Sp E.Carrier)).subtype.comp β
  have hk : (MovedSection.coverProjection s pc.equiv).toLinearMap.ker.toAddSubgroup.toSubgroup.map
      pc.embedding = U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
    apply le_antisymm
    · rintro x ⟨w,hw,rfl⟩
      exact ⟨pc.range_eq ▸ ⟨w,rfl⟩,(pc.kernel w.toAdd).mp hw⟩
    · intro x hx
      obtain ⟨w,rfl⟩ := (pc.range_eq.symm ▸ hx.1 : x ∈ pc.embedding.range)
      exact ⟨w,(pc.kernel w.toAdd).mpr hx.2,rfl⟩
  have hmove : ⁅fixedCore R a,U R z⁆ = ⁅Z R z,fixedCore R a⁆ := by
    rw [commutator_comm]
    exact (original_fixedCore_displacement_eq_moving h hshort hinner g hb path hat hzt).symm
  have hquad : ⁅⁅U R z,fixedCore R a⁆,fixedCore R a⁆=⊥ :=
    le_antisymm ((commutator_mono (commutator_mono (U_le_Z z) le_rfl) le_rfl).trans
      (original_fixedCore_quadratic h hshort hinner hnsyl g hb path hat hzt).le) bot_le
  have hescape : ¬ (MovedSection.coverProjection s pc.equiv).toLinearMap.ker.toAddSubgroup.toSubgroup.map
      pc.embedding ≤ ⁅fixedCore R a,U R z⁆ := by
    rw [hk,hmove]
    intro hle
    have hdis := (original_source_two_large_displacement_disjoint_opposite_fixedCore
      h hshort hinner g hb hnsyl path hat hzt hlarge).1
    have hUQ : U R z ≤ Q R z := (U_le_Z z).trans
      ((g.omega_bound z path.end_color (by
        rw [g.distance_constant z path.end_color]; change 0 < g.b R; omega)).trans
        (omegaCenter_le _))
    have he : U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) = ⊥ := by
      apply bot_unique
      rw [←hdis.eq_bot]
      exact le_inf hle (inf_le_inf_right _ hUQ)
    have hh := (original_source_two_large_fixed_attachment_displacement_card
      h hshort hinner g hb hnsyl path hat hzt hlarge).2.1
    rw [he,card_bot] at hh
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    omega
  obtain ⟨v,hv⟩ := pc.point_image
  have hbound := embedded_point_quadratic_actor_card
    (MovedSection.coverAction s pc.equiv) (MovedSection.coverProjection s pc.equiv) pc.cover
    (U R z) (fixedCore R a) pc.embedding pc.injective pc.range_eq β
    (fun x => pc.actor_conjugation (inclusion hDT x)) hquad hescape α.range
    (by rintro _ ⟨x,rfl⟩; exact ⟨inclusion hDT x,rfl⟩) v hv
  have hδker : δ.ker=(Q R z).subgroupOf (fixedCore R a) := by
    change (α.comp (inclusion hDT)).ker=_
    rw [←MonoidHom.comap_ker,pc.actor_kernel,comap_inclusion_subgroupOf]
  have hi : (Q R z).relIndex (fixedCore R a)=Nat.card δ.range := by
    rw [relIndex,←hδker,index_ker]
  rw [hi]
  simpa only [E,pc.field.card_eq,pc.degree] using hbound

/-- Both index bounds in the original full-radical product are attained. -/
theorem original_source_two_large_fixedCore_exact_indices
    (g : Geometry R) (hb : g.b R = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z)) :
    (Q R z).relIndex (fixedCore R a) = 2^n ∧
      ((Q R t ⊓ Ltilde R a) ⊔ fixedCore R a).relIndex (Q R t) = 2^n := by
  have ht : color R t = true := by
    cases he : color R t with
    | false => exact (adjacent_color_ne R hat (path.start_color.trans he.symm)).elim
    | true => rfl
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSa : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  let := finite_stabilizer R z
  let : Finite (Q R t) := Finite.of_injective
    (inclusion hTSz) (inclusion_injective _)
  let : (((Q R t ⊓ Ltilde R a)).subgroupOf (Q R t)).Normal :=
    normal_subgroupOf_of_le_normalizer (original_componentRadical_normalized hat)
  let : ((Q R z).subgroupOf (Q R t)).Normal := normal_subgroupOf_of_le_normalizer (hTSz.trans (Q_normalized R z))
  have hAT : (Q R t ⊓ Ltilde R a) ≤ Q R t := inf_le_left
  have hDT : fixedCore R a ≤ Q R t := inf_le_left.trans hQaT
  have hi := index_le_three_factors
    (((Q R t ⊓ Ltilde R a)).subgroupOf (Q R t))
    ((fixedCore R a).subgroupOf (Q R t))
    ((Q R z).subgroupOf (Q R t))
  rw [←subgroupOf_sup hAT hDT,relIndex_subgroupOf hAT,relIndex_subgroupOf hDT] at hi
  change (Q R z).relIndex (Q R t) ≤
    ((Q R t ⊓ Ltilde R a) ⊔ fixedCore R a).relIndex (Q R t) *
      ((Q R z).relIndex ((Q R t ⊓ Ltilde R a)) *
        (Q R z).relIndex (fixedCore R a)) at hi
  rw [original_nonsylow_full_radical_card h hinner hnsyl path.end_color hzt,
    (original_large_movement_images h hshort hinner hnsyl g hb path hat hzt hlarge).1] at hi
  have hD := original_source_two_large_fixedCore_actor_index_le_field h hshort hinner g hb hnsyl path hat hzt hlarge
  have hT := (original_component_fixedCore_relIndex h hshort hinner path.start_color hat).2
  have hq : 0 < 2^n := by positivity
  have hDge : 2^n ≤ (Q R z).relIndex (fixedCore R a) := by
    have hh := hi.trans (Nat.mul_le_mul_right _ hT)
    have hh' : (2^n)^2 * 2^n ≤ (2^n)^2 * (Q R z).relIndex (fixedCore R a) := by
      nlinarith only [hh]
    exact Nat.le_of_mul_le_mul_left hh' (by positivity)
  have hDeq := le_antisymm hD hDge
  rw [hDeq] at hi
  have hTge : 2^n ≤ ((Q R t ⊓ Ltilde R a) ⊔ fixedCore R a).relIndex (Q R t) := by
    have hh' : 2^n * (2^n)^2 ≤
        ((Q R t ⊓ Ltilde R a) ⊔ fixedCore R a).relIndex (Q R t) * (2^n)^2 := by
      nlinarith only [hi]
    exact Nat.le_of_mul_le_mul_right hh' (by positivity)
  exact ⟨hDeq,le_antisymm hT hTge⟩

/-- The critical centralizer has at most three natural field dimensions after
factoring by the entire opposite fixed core. -/
theorem original_critical_core_centralizer_fixedCore_index_le_cube
    {g : Geometry R} {a z : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2) :
    (fixedCore R z).relIndex
      (Q R z ⊓ centralizer (Z R a : Set (FreeAmalgam R))) ≤ (2^n)^3 := by
  classical
  obtain ⟨E,hE,s,γ,hγinj,hγ,hmap,i,hi,hd,hrange,_⟩ :=
    short_original_wholeKernel_natural_dualCover h hshort path.end_color
  have hCtop : K.map (QuotientGroup.mk' (pCore 2 H))=⊤ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hh := congrArg (fun A : Subgroup H => A.map q)
      hinner
    rw [Subgroup.map_sup,show (pCore 2 H).map q=⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  have hγonto : Function.Surjective γ := MonoidHom.range_eq_top.mp (hγ.trans hCtop)
  let C := Q R z ⊓ centralizer (Z R a : Set (FreeAmalgam R))
  let B := s.sectionData.imageSpace C
  have hUQ : U R z ≤ Q R z := (U_le_Z z).trans
    ((g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]; change 0 < g.b R; omega)).trans
      (omegaCenter_le _))
  have himage : s.sectionData.imageSpace (U R z) = i.toLinearMap.range := by
    ext w
    rw [hrange,s.sectionData.mem_imageSpace_iff]
  have hB : B ≤ i.toLinearMap.range := by
    have hh := s.sectionData.imageSpace_mono
      (short_original_critical_core_centralizer_le_moving_fixed h hshort (by omega) path)
    change B ≤ s.sectionData.imageSpace (U R z ⊔
      (Q R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)))) at hh
    rw [s.sectionData.imageSpace_sup_kernel _ hUQ,himage] at hh
    exact hh
  have hZaS : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  obtain ⟨x,hx,hxQ⟩ := SetLike.not_le_iff_exists.mp path.critical.2
  let xS : stabilizer R z := ⟨x,hZaS hx⟩
  obtain ⟨b,hb'⟩ := hγonto (s.quotient xS)
  have hbne : b.val ≠ 1 := by
    intro he
    have hb1 : b=1 := Subtype.ext he
    have hxker : xS ∈ s.quotient.ker := by
      change s.quotient xS=1
      rw [←hb',hb1,map_one]
    apply hxQ
    have hh := mem_map_of_mem (stabilizer R z).subtype hxker
    rw [s.quotient_kernel] at hh
    exact hh
  let P : Submodule E.Carrier (Vector E.Carrier) :=
    ((symplecticNatural 2 b.val)-LinearMap.id).ker
  have hPne : P ≠ ⊤ := by
    intro he
    apply hbne
    apply Subtype.ext
    ext k l
    have hf : (Pi.single l 1 : Vector E.Carrier) ∈ P := he ▸ Submodule.mem_top
    change (symplecticNatural 2 b.val (Pi.single l 1))-Pi.single l 1=0 at hf
    rw [symplecticNatural_apply] at hf
    have heq := congrFun (sub_eq_zero.mp hf) k
    simpa [Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,Matrix.mulVec_single,
      Pi.single_apply,Matrix.one_apply] using heq
  have hdim : Module.finrank E.Carrier P ≤ 3 := by
    have hh := Submodule.finrank_lt hPne
    have hV : Module.finrank E.Carrier (Vector E.Carrier)=4 := by simp [Theory.SpecificGroups.SymplecticFour.Vector]
    rw [hV] at hh
    omega
  have hfix (v : B) : s.action (γ b) v.val=v.val := by
    rw [hb']
    exact s.sectionData.fixed_on_imageSpace_of_commutator_le (Z R a) C
      ((commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mpr (show C ≤ centralizer (Z R a : Set (FreeAmalgam R)) from inf_le_right))).le.trans bot_le)
      xS hx v.val v.property
  have hex (v : B) : ∃ w : Vector E.Carrier, i w=v.val := hB v.property
  choose f hf using hex
  let fP : B → P := fun v => ⟨f v,by
    change b.val • f v-f v=0
    apply sub_eq_zero.mpr
    apply hi
    change i (binaryNatural b (f v))=i (f v)
    rw [i.isIntertwining,hf]
    exact hfix v⟩
  have hfi : Function.Injective fP := by
    intro v w he
    apply Subtype.ext
    rw [←hf v,←hf w]
    exact congrArg i (congrArg Subtype.val he)
  have hcard : Nat.card B ≤ Nat.card E.Carrier^3 :=
    (Nat.card_le_card_of_injective fP hfi).trans (by
      rw [Module.natCard_eq_pow_finrank (K := E.Carrier)]
      exact Nat.pow_le_pow_right Nat.card_pos hdim)
  rw [s.sectionData.imageSpace_card_eq_relIndex C inf_le_left,E.card_eq,hE] at hcard
  exact hcard

/-- The first full fixed-core comparison on printed p.874. -/
theorem original_source_two_large_fixedCore_overlap_index_le
    (g : Geometry R) (hb : g.b R = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z)) :
    (fixedCore R z).relIndex (fixedCore R a ⊓ Q R z) ≤ (2^n)^3 ∧
      (fixedCore R z).relIndex (fixedCore R a) ≤ (2^n)^4 := by
  have ht : color R t = true := by
    cases he : color R t with
    | false => exact (adjacent_color_ne R hat (path.start_color.trans he.symm)).elim
    | true => rfl
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSa : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  let := finite_stabilizer R z
  let : Finite (Q R t) := Finite.of_injective
    (inclusion hTSz) (inclusion_injective _)
  let : Finite (fixedCore R a) := Finite.of_injective
    (inclusion (inf_le_left.trans hQaT)) (inclusion_injective _)
  let C := Q R z ⊓ centralizer (Z R a : Set (FreeAmalgam R))
  let : Finite C := Finite.of_injective
    (inclusion (inf_le_left.trans hQzT)) (inclusion_injective _)
  have hsub : fixedCore R a ⊓ Q R z ≤ C := by
    refine le_inf inf_le_right ?_
    apply (inf_le_left.trans (show fixedCore R a ≤ Q R a from inf_le_left)).trans
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q R a path.start_color))
  have hcube := (relIndex_le_of_le_right hsub index_ne_zero_of_finite).trans
    (original_critical_core_centralizer_fixedCore_index_le_cube h hshort hinner path hb)
  refine ⟨hcube,?_⟩
  have hh := relIndex_inf_mul_relIndex (fixedCore R z) (Q R z) (fixedCore R a)
  rw [inf_eq_left.mpr (show fixedCore R z ≤ Q R z from inf_le_left),
    inf_comm (Q R z) (fixedCore R a),
    (original_source_two_large_fixedCore_exact_indices h hshort hinner g hb hnsyl path hat hzt hlarge).1] at hh
  rw [←hh]
  calc
    _ ≤ (2^n)^3 * 2^n := Nat.mul_le_mul_right _ hcube
    _ = (2^n)^4 := (pow_succ _ 3).symm

private theorem original_source_two_large_component_fixedCore_intersection_index_le
    (g : Geometry R) (hb : g.b R = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z)) :
    let T₁ := (Q R t ⊓ Ltilde R a) ⊔ fixedCore R z
    T₁.relIndex (fixedCore R a) ≤ (2^n)^3 := by
  have ht : color R t = true := by
    cases he : color R t with
    | false => exact (adjacent_color_ne R hat (path.start_color.trans he.symm)).elim
    | true => rfl
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSa : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  let T₁ := (Q R t ⊓ Ltilde R a) ⊔ fixedCore R z
  let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
  change T₁.relIndex (fixedCore R a) ≤ (2^n)^3
  let := finite_stabilizer R z
  let : Finite (Q R t) := Finite.of_injective
    (inclusion hTSz) (inclusion_injective _)
  have hBT : (Q R t ⊓ Ltilde R a) ≤ Q R t := inf_le_left
  have hDT : fixedCore R a ≤ Q R t := inf_le_left.trans hQaT
  have hD'T : fixedCore R z ≤ Q R t := inf_le_left.trans hQzT
  have hT₁T : T₁ ≤ Q R t := sup_le hBT hD'T
  let : Finite (fixedCore R a) := Finite.of_injective
    (inclusion hDT) (inclusion_injective _)
  let : Finite (T₁ ⊓ fixedCore R a : Subgroup (FreeAmalgam R)) := Finite.of_injective
    (inclusion (show T₁ ⊓ fixedCore R a ≤ fixedCore R a from inf_le_right))
    (inclusion_injective _)
  have hUAQ : U R a ≤ Q R a := (U_le_Z a).trans
    ((g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)).trans
      (omegaCenter_le _))
  have hAD : A ≤ fixedCore R a := inf_le_inf_right _ hUAQ
  have hAB : A ≤ (Q R t ⊓ Ltilde R a) :=
    inf_le_left.trans ((le_inf ((original_component_core_intersection h hshort path.start_color).ge.trans (inf_le_right.trans hQaT))
      ((original_component_core_intersection h hshort path.start_color).ge.trans inf_le_left)))
  have hAinside : A ≤ T₁ ⊓ fixedCore R a := le_inf (hAB.trans le_sup_left) hAD
  have hdis := (original_source_two_large_displacement_disjoint_opposite_fixedCore
    h hshort hinner g hb hnsyl path hat hzt hlarge).2
  have hAcard := (original_source_two_large_fixed_attachment_displacement_card
    h hshort hinner g hb hnsyl path hat hzt hlarge).1
  have hAi : (fixedCore R z).relIndex A=2^n := by
    rw [←inf_relIndex_right,inf_comm]
    change (A ⊓ fixedCore R z).relIndex A=2^n
    rw [hdis.eq_bot,relIndex_bot_left]
    exact hAcard
  have hlow := relIndex_le_of_le_right (H := fixedCore R z)
    hAinside (show (fixedCore R z).relIndex (T₁ ⊓ fixedCore R a) ≠ 0 from
      index_ne_zero_of_finite)
  rw [hAi] at hlow
  have hmul := relIndex_inf_mul_relIndex (fixedCore R z) T₁ (fixedCore R a)
  rw [inf_eq_left.mpr (show fixedCore R z ≤ T₁ from le_sup_right)] at hmul
  have hupper := (original_source_two_large_fixedCore_overlap_index_le
    h hshort hinner g hb hnsyl path hat hzt hlarge).2
  have hD : T₁.relIndex (fixedCore R a) ≤ (2^n)^3 := by
    have hh := (Nat.mul_le_mul_right (T₁.relIndex (fixedCore R a)) hlow).trans
      (hmul.trans_le hupper)
    have hh' : 2^n * T₁.relIndex (fixedCore R a) ≤ 2^n * (2^n)^3 := by
      nlinarith only [hh]
    exact Nat.le_of_mul_le_mul_left hh' (by positivity)
  exact hD

/-- The source subgroup T₁ = T₀D′ has index at most q⁴; its intersection
with D has index at most q³. Both complete fixed cores remain in the formula. -/
theorem original_source_two_large_component_fixedCore_index_upper
    (g : Geometry R) (hb : g.b R = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z)) :
    let T₁ := (Q R t ⊓ Ltilde R a) ⊔ fixedCore R z
    T₁.relIndex (fixedCore R a) ≤ (2^n)^3 ∧
      T₁.relIndex (Q R t) ≤ (2^n)^4 := by
  have ht : color R t = true := by
    cases he : color R t with
    | false => exact (adjacent_color_ne R hat (path.start_color.trans he.symm)).elim
    | true => rfl
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  let T₁ := (Q R t ⊓ Ltilde R a) ⊔ fixedCore R z
  change T₁.relIndex (fixedCore R a) ≤ (2^n)^3 ∧ T₁.relIndex (Q R t) ≤ (2^n)^4
  have hD := original_source_two_large_component_fixedCore_intersection_index_le
    h hshort hinner g hb hnsyl path hat hzt hlarge
  let := finite_stabilizer R z
  let : Finite (Q R t) := Finite.of_injective (inclusion hTSz) (inclusion_injective _)
  have hBT : (Q R t ⊓ Ltilde R a) ≤ Q R t := inf_le_left
  have hDT : fixedCore R a ≤ Q R t := inf_le_left.trans hQaT
  refine ⟨hD,?_⟩
  have hD'T : fixedCore R z ≤ Q R t := inf_le_left.trans (Q_le_adjacent_h R ht hzt)
  have hJT : T₁ ≤ Q R t := sup_le hBT hD'T
  have hJn : Q R t ≤ normalizer (T₁ : Set (FreeAmalgam R)) :=
    (le_inf (original_componentRadical_normalized hat) (original_fixedCore_normalized hzt)).trans
      (normalizer_inf_normalizer_le_normalizer_sup (Q R t ⊓ Ltilde R a) (fixedCore R z))
  have hi := index_le_product_of_component_le (Q R t) (Q R t ⊓ Ltilde R a)
    (fixedCore R a) T₁ hBT hDT hJT le_sup_left hJn
  have hr := (original_component_fixedCore_relIndex h hshort hinner path.start_color hat).2
  calc
    T₁.relIndex (Q R t) ≤ ((Q R t ⊓ Ltilde R a) ⊔ fixedCore R a).relIndex (Q R t) *
        T₁.relIndex (fixedCore R a) := hi
    _ ≤ 2^n * (2^n)^3 := Nat.mul_le_mul hr hD
    _ = (2^n)^4 := by ring

/-- The fixed-core index squeeze excludes the large-movement branch with
both full fixed attachments and the actual point-radical cover retained. -/
theorem original_source_two_large_movement_false
    (g : Geometry R) (hb : g.b R = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z)) : False := by
  have ht : color R t = true := by
    cases he : color R t with
    | false => exact (adjacent_color_ne R hat (path.start_color.trans he.symm)).elim
    | true => rfl
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSa : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  let := h.component_normal
  let s := originalMovedSection h
  let := finite_stabilizer R z
  let : Finite (Q R t) := Finite.of_injective
    (inclusion hTSz) (inclusion_injective _)
  obtain ⟨pc⟩ := original_source_two_large_radical_point_cover h hinner g hb hnsyl path hat hzt hlarge
  have hUQ : U R z ≤ Q R z := (U_le_Z z).trans
    ((g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]; change 0 < g.b R; omega)).trans
      (omegaCenter_le _))
  have hDT : fixedCore R a ≤ Q R t := inf_le_left.trans hQaT
  have hUT : U R z ≤ Q R t := hUQ.trans hQzT
  let β := pc.actor.comp (inclusion hDT)
  have hker (w : s.space.toSubmodule) : MovedSection.coverProjection s pc.equiv w=0 ↔
      pc.embedding (Multiplicative.ofAdd w) ∈ fixedCore R z := by
    rw [pc.kernel w]
    exact ⟨fun hw => ⟨hUQ (pc.range_eq ▸ ⟨_,rfl⟩),hw⟩,fun hw => hw.2⟩
  have hpre := cover_commutatorPreimage_le_fixed
    (MovedSection.coverAction s pc.equiv) (MovedSection.coverProjection s pc.equiv) pc.cover
    (U R z) (fixedCore R a) (fixedCore R z)
    pc.embedding pc.injective pc.range_eq β
    (fun x => pc.actor_conjugation (inclusion hDT x)) (hUT.trans (original_fixedCore_normalized hzt)) hker
  have hBD : ⁅(Q R t ⊓ Ltilde R a),fixedCore R a⁆=⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply (show (Q R t ⊓ Ltilde R a) ≤ Ltilde R a from inf_le_right).trans
    exact le_centralizer_iff.mpr (show fixedCore R a ≤
      centralizer (Ltilde R a : Set (FreeAmalgam R)) from inf_le_right)
  let C := ⁅Z R z,fixedCore R a⁆
  have hCU : C ≤ U R z := by
    rw [show C=⁅U R z,fixedCore R a⁆ from
      original_fixedCore_displacement_eq_moving h hshort hinner g hb path hat hzt]
    exact le_normalizer_iff_commutator_le_left.mp
      (hDT.trans (hTSz.trans (U_normalized z)))
  have hZzT : Z R z ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
      g.distance_constant z path.end_color]
    change 1 < g.b R
    omega
  have hCD : C ≤ fixedCore R a :=
    le_normalizer_iff_commutator_le_right.mp (hZzT.trans (original_fixedCore_normalized hat))
  have hCf : ⁅C,fixedCore R a⁆=⊥ :=
    original_fixedCore_quadratic h hshort hinner hnsyl g hb path hat hzt
  have hCe := (original_source_two_large_displacement_disjoint_opposite_fixedCore
    h hshort hinner g hb hnsyl path hat hzt hlarge).1
  have hCc := (original_source_two_large_fixed_attachment_displacement_card
    h hshort hinner g hb hnsyl path hat hzt hlarge).2.2.1
  exact source_index_contradiction (Q R t) ((Q R t ⊓ Ltilde R a))
    (fixedCore R a) (fixedCore R z) (Q R z) (U R z) C
    (2^n) (one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega))
    inf_le_left hDT inf_le_left hUQ hQzT
    (original_componentRadical_normalized hat) (original_fixedCore_normalized hat) (original_fixedCore_normalized hzt)
    (hTSz.trans (Q_normalized R z)) (hTSz.trans (U_normalized z))
    hBD hCU hCD hCf hCe hCc
    (original_source_two_large_fixedCore_movement_eq_square h hshort hinner g hb hnsyl path hat hzt hlarge)
    hpre (original_nonsylow_full_radical_card h hinner hnsyl path.end_color hzt)
    (original_large_movement_images h hshort hinner hnsyl g hb path hat hzt hlarge).1
    (original_source_two_large_fixedCore_overlap_index_le h hshort hinner g hb hnsyl path hat hzt hlarge).2
    (original_source_two_large_component_fixedCore_index_upper h hshort hinner g hb hnsyl path hat hzt hlarge).2
    (original_component_fixedCore_relIndex h hshort hinner path.start_color hat).2

/-- The small-movement subcase of MS93 (3.7)(2). Its index is measured
on the original opposite natural cover; the entire Q acts and the common
edge center and both complete fixed attachments are retained. -/
theorem original_source_two_of_small_core_movement
    (g : Geometry R) (hb : g.b R = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hsmall : (centralizer (Q R a : Set (FreeAmalgam R))).relIndex
      (U R z) ≤ (2^n)^2) :
    ⁅Z R z,Q R a⁆ ≤ Z R t := by
  have ht : color R t = true := by
    cases he : color R t with
    | false => exact (adjacent_color_ne R hat (path.start_color.trans he.symm)).elim
    | true => rfl
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSa : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  have hZzT : Z R z ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
      g.distance_constant z path.end_color]
    change 1 < g.b R
    omega
  have hZt : Z R t = omegaCenter (Q R t) := by simp [Z,ht,edgeOmega]
  have hcentral : Z R t ≤ centralizer (Q R a : Set (FreeAmalgam R)) := by
    rw [hZt]
    exact fun x hx y hy => (mem_omegaCenter_iff.mp hx).2.2 y (hQaT hy)
  have hUQ : U R z ≤ normalizer (Q R a : Set (FreeAmalgam R)) :=
    ((U_le_Z z).trans hZzT).trans (hTSa.trans (Q_normalized R a))
  have heq : ⁅Z R z,Q R a⁆ = ⁅U R z,Q R a⁆ := by
    apply le_antisymm ?_ (commutator_mono (U_le_Z z) le_rfl)
    rw [commutator_comm (Z R z),commutator_comm (U R z)]
    apply commutator_le_moving_of_inner_mod_centralizer (Q R a) (U R z)
      (Z R z) hUQ
    rw [original_Z_eq_moving_sup_edge h hshort hinner g hb path.end_color hzt]
    exact sup_le_sup_left hcentral _
  have hquad := original_moving_quadratic_of_small_index h hinner path.end_color
    (Q R a) (hQaT.trans hTSz)
    (Q_isPGroup R h.radical.isPGroup h.radical.twoCore_le a path.start_color) hsmall
  have hfull := (original_component_radical_triples h hshort hinner hnsyl g hb path hat hzt).2
  have hcentralT : ⁅Z R z,Q R a⁆ ≤
      centralizer (Q R t : Set (FreeAmalgam R)) := by
    apply le_centralizer_iff.mp
    rw [←original_component_radical_sup_core h hinner path.start_color hat]
    apply sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hfull))
    apply le_centralizer_iff.mp
    rw [heq]
    exact commutator_eq_bot_iff_le_centralizer.mp hquad
  have hWZ : ⁅Z R z,Q R a⁆ ≤ Z R z := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp
      ((hQaT.trans hTSz).trans (Z_normalized R z))
  have hZX := g.omega_bound z path.end_color (by
    rw [g.distance_constant z path.end_color]; change 0 < g.b R; omega)
  rw [hZt]
  intro x hx
  exact mem_omegaCenter_iff.mpr ⟨hZzT (hWZ hx),
    (mem_omegaCenter_iff.mp (hZX (hWZ hx))).2.1,hcentralT hx⟩
/-- The midpoint containment of MS93 (3.7)(2), with no extra movement bound. -/
theorem original_source_two_midpoint_containment
    (g : Geometry R) (hb : g.b R = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    :
    ⁅Z R z,Q R a⁆ ≤ Z R t := by
  apply original_source_two_of_small_core_movement h hshort hinner g hb hnsyl path hat hzt
  exact le_of_not_gt (original_source_two_large_movement_false h hshort hinner g hb hnsyl path hat hzt)
omit hshort hinner in
/-- MS93 (3.7)(2) on the selected original marked star. Every critical
path of length two has its opposite-core displacement in the common edge
center, without a small-movement or minimum-saturation premise. -/
theorem exists_source_star_midpoint_containment
    (d : CharacteristicReduction K R) (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h)) :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R,
      Y.map (embedS R) = componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      d.subgroup ≤ starCentralizer R Y ∧
      (let T := (starCentralizer R Y).map R.subtype
       let M := K ⊔ T
       let S := T.subgroupOf M
       ∃ hs : Input (K.subgroupOf M) S n F, ∃ gs : Geometry S,
         hs.quotientEquiv = (subgroupOfCoreQuotientEquiv le_sup_left).trans h.quotientEquiv ∧
         S = R.subgroupOf M ∧
         (normalizer (S : Set M)).pCoreIn 2 = S ∧
         ((T.subgroupOf K).map (componentProjection h)) =
           (R.subgroupOf K).map (componentProjection h) ∧
         gs.b S = 2 ∧
         ∀ (a z t : Vertex S) (_path : CriticalPath S gs a z),
           Adjacent S a t → Adjacent S z t →
           ⁅Z S z,Q S a⁆ ≤ Z S t) := by
  obtain ⟨P,Y,hY,hn,hmin,hs,hquot,hrest,hsat,hinner,hmark,hsyl,gs,hgs⟩ :=
    exists_source_star_intrinsic_distance_two h d g hb
  have hshort := (short_and_natural_of_distance_two h d g hb).1
  have hstarshort : IsShort (K.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype)) :=
    hshort.of_mulEquiv (subgroupOfEquivOfLe le_sup_left).symm
  have hstar_nsyl : ¬ ∃ S' : Sylow 2 (Sp F), (S' : Subgroup (Sp F)) =
      ((((starCentralizer R Y).map R.subtype).subgroupOf
        (K ⊔ (starCentralizer R Y).map R.subtype)).subgroupOf
          (K.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype))).map (componentProjection hs) := by
    intro he
    exact hnsyl ((original_sylow_iff_marked_sylow h).mp
      (hsyl.mp ((original_sylow_iff_marked_sylow hs).mpr he)))
  refine ⟨P,Y,hY,hn,hmin,hs,gs,hquot,hrest,hsat,hmark,hgs,?_⟩
  intro a z t path hat hzt
  exact original_source_two_midpoint_containment hs hstarshort hinner gs hgs hstar_nsyl path hat hzt

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
