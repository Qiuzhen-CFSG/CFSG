module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceSixCritical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourRadicalGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceThreeMovement
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourRadicalGeneration

/-!
# Original-star whole-core displacement in MS93 (3.7)(6)

For a large original critical pair, the whole-core displacement has exactly
its natural fixed index modulo the complete fixed attachment. Consequently
an actor with fixed index q cannot fill the full radical movement of index
q squared, even after adjoining the attachment.

The internal imports reuse the original midpoint central supplement and
generic cover-index calculations. All geometry, quotient actions and full kernels here belong
to the original radical. Source: Meierfrankenfeld--Stellmacher (1993),
(3.7)(6), printed p.876.
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

/-- The whole-core displacement has at most the natural fixed index, even
before the whole core has collapsed. The complete fixed attachment is retained. -/
private theorem whole_core_displacement_bound
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (B : Subgroup (FreeAmalgam R)) (hB : B ≤ Z R z) :
    (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))).relIndex
      ⁅Q R a,B⁆ ≤
      (centralizer (B : Set (FreeAmalgam R))).relIndex (Z R a) := by
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  obtain ⟨⟨cv⟩,_,_,_,hRa,hRz,_⟩ :=
    original_source_four_large_paired_geometry h hshort hinner hnsyl g hb path hat hzt hcritical
  let A := U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
  let D := fixedCore R a
  let N := ⁅U R a,B⁆
  let M := ⁅Q R a,B⁆
  have hUQ : U R a ≤ Q R a := (U_le_Z a).trans
    ((g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0<g.b R; omega)).trans
      (omegaCenter_le _))
  have hBT : B ≤ Q R t := hB.trans
    ((g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]; change 0<g.b R; omega)).trans
      ((omegaCenter_le _).trans (Q_le_adjacent_h R ht hzt)))
  have hBS := hBT.trans (show Q R t ≤ stabilizer R a from fun _ hx => hx.2 _ (adjacent_symm R hat))
  have hMU : M ≤ U R a := by
    have hm : M ≤ ⁅Z R a,Q R t⁆ := by
      rw [hRa,←hRz,commutator_comm]
      exact commutator_mono (Q_le_adjacent_h R ht hat) hB
    exact hm.trans (original_full_radical_Z_displacement_le_moving h hinner path.start_color hat)
  have hNU : N ≤ U R a := by
    dsimp only [N]
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp (hBS.trans (U_normalized a))
  have hMQ := hMU.trans hUQ
  have hDQ : D ≤ Q R a := inf_le_left
  let := finite_stabilizer R a
  let : Finite (Q R a) := Finite.of_injective
    (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1))
    (inclusion_injective _)
  let : Finite (Z R a) := finite_Z R a
  let : Finite D := Finite.of_injective (inclusion hDQ) (inclusion_injective _)
  let : Finite M := Finite.of_injective (inclusion hMQ) (inclusion_injective _)
  let : Finite N := Finite.of_injective (inclusion (hNU.trans hUQ)) (inclusion_injective _)
  let : Finite (↥(N ⊔ D)) := Finite.of_injective
    (inclusion (sup_le (hNU.trans hUQ) hDQ)) (inclusion_injective _)
  have hnormal : D ≤ normalizer (N : Set (FreeAmalgam R)) := by
    apply (show D ≤ centralizer (N : Set (FreeAmalgam R)) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    intro x hx y hy
    exact ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a path.start_color))
      (U_le_Z a (hNU hy)) x (hDQ hx)).symm
  have hDM : D ⊓ M=A ⊓ M := by
    ext x
    exact ⟨fun hx => ⟨⟨hMU hx.2,hx.1.2⟩,hx.2⟩,
      fun hx => ⟨⟨hUQ hx.1.1,hx.1.2⟩,hx.2⟩⟩
  have hDN : D ⊓ N=A ⊓ N := by
    ext x
    exact ⟨fun hx => ⟨⟨hNU hx.2,hx.1.2⟩,hx.2⟩,
      fun hx => ⟨⟨hUQ hx.1.1,hx.1.2⟩,hx.2⟩⟩
  calc
    A.relIndex M = D.relIndex M := by rw [←inf_relIndex_right A M,←hDM,inf_relIndex_right]
    _ ≤ D.relIndex (N ⊔ D) := relIndex_le_of_le_right
      (original_whole_core_displacement_le h hshort hinner path.start_color B hBS) index_ne_zero_of_finite
    _ = D.relIndex N := relIndex_sup_of_normalizes N D hnormal
    _ = A.relIndex N := by rw [←inf_relIndex_right D N,hDN,inf_relIndex_right]
    _ = (centralizer (B : Set (FreeAmalgam R))).relIndex (U R a) := by
      rw [show N=⁅B,U R a⁆ from commutator_comm _ _]
      exact SaturatedDistanceTwo.plane_cover_displacement_index cv B hBT
    _ ≤ (centralizer (B : Set (FreeAmalgam R))).relIndex (Z R a) :=
      relIndex_le_of_le_right (U_le_Z a) index_ne_zero_of_finite

/-- The whole-core displacement has exactly the natural fixed index, even
before the whole core has collapsed. The complete fixed attachment is retained. -/
theorem original_source_six_whole_core_displacement_index
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (B : Subgroup (FreeAmalgam R)) (hB : B ≤ Z R z) :
    (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))).relIndex
      ⁅Q R a,B⁆ =
      (centralizer (B : Set (FreeAmalgam R))).relIndex (Z R a) := by
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  have hupper := whole_core_displacement_bound h hshort hinner hnsyl g hb path hat hzt hcritical B hB
  obtain ⟨⟨cv⟩,_,_,_,_⟩ :=
    original_source_four_large_paired_geometry h hshort hinner hnsyl g hb path hat hzt hcritical
  have hUQ : U R a ≤ Q R a := (U_le_Z a).trans
    ((g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0<g.b R; omega)).trans
      (omegaCenter_le _))
  have hBT : B ≤ Q R t := hB.trans
    ((g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]; change 0<g.b R; omega)).trans
      ((omegaCenter_le _).trans (Q_le_adjacent_h R ht hzt)))
  let := finite_stabilizer R a
  let := finite_Z R a
  let : Finite (Q R a) := Finite.of_injective
    (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1))
    (inclusion_injective _)
  have hMQ : ⁅Q R a,B⁆ ≤ Q R a := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp ((hBT.trans (show Q R t ≤ stabilizer R a from fun _ hx => hx.2 _ (adjacent_symm R hat))).trans (Q_normalized R a))
  let : Finite (⁅Q R a,B⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hMQ) (inclusion_injective _)
  have hnatural := SaturatedDistanceTwo.plane_cover_displacement_index cv B hBT
  let := g.Z_elementary (by omega) a path.start_color
  have hCT : Z R t ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
    rw [show Z R t=omegaCenter (Q R t) by simp [Z,ht,edgeOmega]]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  have hfixed := central_supplement_fixed_index (U R a) (Z R t) (Z R a) B
    (U_le_Z a) (Sp4Four.edge_Z_le_endpoint R path.start_color hat)
    (original_Z_eq_moving_sup_edge h hshort hinner g hb path.start_color hat)
    (hCT.trans (centralizer_le hBT))
  apply le_antisymm hupper
  rw [hfixed,←hnatural,commutator_comm B]
  exact relIndex_le_of_le_right (commutator_mono hUQ le_rfl) index_ne_zero_of_finite

/-- The source-(6) whole-core displacement cannot fill the full radical
movement, even after adjoining the entire fixed attachment. -/
theorem original_source_six_whole_core_movement_ne_full
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a))
    (B : Subgroup (FreeAmalgam R)) (hB : B ≤ Z R z)
    (hindex : (centralizer (B : Set (FreeAmalgam R))).relIndex (Z R a)=2^n) :
    let A := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
    A.relIndex ⁅Q R a,B⁆ = 2^n ∧
      ⁅Q R a,B⁆ ⊔ A ≠ ⁅Z R z,Q R t⁆ := by
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  let A := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
  let M := ⁅Q R a,B⁆
  have hAe : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))=A :=
    original_source_four_fixed_attachments h hshort hinner hnsyl g hb path hat hzt
  have hbound : A.relIndex M = 2^n := by
    have hh := original_source_six_whole_core_displacement_index h hshort hinner hnsyl g hb path hat hzt hcritical B hB
    rwa [hAe,hindex] at hh
  refine ⟨hbound,?_⟩
  intro he
  have hgeom := original_source_four_large_paired_geometry h hshort hinner hnsyl g hb path hat hzt hcritical
  have hMU : M ≤ U R a := by
    have hh : M ≤ ⁅Z R a,Q R t⁆ := by
      rw [hgeom.2.2.2.2.1,←hgeom.2.2.2.2.2.1,commutator_comm]
      exact commutator_mono (Q_le_adjacent_h R ht hat) hB
    exact hh.trans (original_full_radical_Z_displacement_le_moving h hinner path.start_color hat)
  let := g.Z_elementary (by omega) a path.start_color
  have hAN : A ≤ normalizer (M : Set (FreeAmalgam R)) :=
    ((hAe.symm.le.trans inf_le_left).trans (U_le_Z a)).trans
      (((Z R a).le_centralizer.trans (centralizer_le (hMU.trans (U_le_Z a)))).trans
        (Subgroup.centralizer_le_normalizer _))
  let := finite_Z R z
  let : Finite A := Finite.of_injective
    (inclusion (show A ≤ Z R z from inf_le_left.trans (U_le_Z z))) (inclusion_injective _)
  have hi := relIndex_sup_of_normalizes M A hAN
  rw [he,hgeom.2.2.2.2.2.1] at hi
  have hc := (original_source_four_large_displacement_order h hshort hinner hnsyl g hb path hat hzt hcritical).2.1
  change A.relIndex ⁅Z R a,Z R z⁆=(2^n)^2 at hc
  rw [hc] at hi
  have hq : 1<2^n := one_lt_pow₀ (by decide : 1<(2:ℕ)) (by have := h.nonbinary; omega)
  nlinarith only [hbound,hi,hq]

/-- The literal source-(6) selection with its exact whole-core displacement
index and the exclusion of full radical movement. -/
theorem original_source_six_field_pair_or_small_whole_core_movement
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a)) :
    ∃ x ∈ Z R z, x ∉ Q R a ∧
      Z R a ⊓ centralizer ({x} : Set (FreeAmalgam R))=Z R t ∧
      ∃ y ∈ stabilizer R a, ∃ k ∈ stabilizer R t,
        (∀ u ∈ Q R t, (MulAut.conj k) u=(MulAut.conj y) u) ∧
        x⁻¹*(y*x*y⁻¹) ∈ Q R a ∧ Commute x (y*x*y⁻¹) ∧
        y ∉ normalizer (((Z R z ⊔ Q R a) : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) ∧
        Nonempty (CriticalPath R g (act R k⁻¹ z) z) ∧
        ((Q R z).relIndex (Z R (act R k⁻¹ z))=2^n ∨
          (y*x*y⁻¹ ∉ Q R z ∧
            (Z R z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam R))).relIndex
              (Z R z)=2^n ∧
            (Q R (act R k⁻¹ z)).relIndex
              (Z R z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam R)))=2^n ∧
            (centralizer ((Z R z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam R))) :
              Set (FreeAmalgam R))).relIndex (Z R (act R k⁻¹ z))=2^n ∧
            (U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))).relIndex
              ⁅Q R (act R k⁻¹ z),
                Z R z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam R))⁆ = 2^n ∧
            ⁅Q R (act R k⁻¹ z),
                Z R z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam R))⁆ ⊔
              (U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))) ≠
                ⁅Z R z,Q R t⁆)) := by
  obtain ⟨x,hx,hxQ,hreg,y,hy,k,hk,he,hcoset,hcomm,hmove,⟨p⟩,halt⟩ :=
    original_source_six_field_pair_or_centralizer_configuration h hshort hinner hnsyl g hb path hat hzt hcritical
  refine ⟨x,hx,hxQ,hreg,y,hy,k,hk,he,hcoset,hcomm,hmove,⟨p⟩,?_⟩
  by_cases hc : (2^n)^2 ≤ (Q R z).relIndex (Z R (act R k⁻¹ z))
  swap
  · apply Or.inl
    simpa only [h.field_card] using (h.original_small_critical_indices_eq_field p (by omega)
      (by simpa only [h.field_card] using lt_of_not_ge hc)).1
  rcases halt with hsmall | ⟨hwQ,hi,hQi,hCi⟩
  · rw [hsmall] at hc
    have hq : 1<2^n := one_lt_pow₀ (by decide : 1<(2:ℕ)) (by have := h.nonbinary; omega)
    exfalso
    nlinarith only [hc,hq]
  apply Or.inr
  refine ⟨hwQ,hi,hQi,hCi,?_⟩
  let v := act R k⁻¹ z
  have hkt : act R k⁻¹ t=t := (stabilizer R t).inv_mem hk
  have hvt : Adjacent R v t := by
    simpa only [hkt] using (adjacent_act_iff R k⁻¹ z t).mpr hzt
  exact original_source_six_whole_core_movement_ne_full h hshort hinner hnsyl g hb p hvt hzt hc
    (Z R z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam R))) inf_le_left hCi


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
