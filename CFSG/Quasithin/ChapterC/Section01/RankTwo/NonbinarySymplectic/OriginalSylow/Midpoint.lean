module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalSylow.MidpointDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoPointDisplacement
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalSylow.MidpointQuadratic
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoRadicalBound

/-!
# Original Sylow midpoint containment

If the opposite core moves more than q squared cosets on the original
natural cover, its component image has order q and its full fixed-core image
has order at most 2q. Their product has index at most q in the full radical,
so the radical quotient has order at most 2q cubed. This contradicts the
literal Sylow quotient order q to the fourth power, since q > 2.

The remaining small movement acts quadratically. The component triple then
makes [Z′,Q] central in the full midpoint radical. Its elementary order puts
it in the entire midpoint edge center, as asserted by MS93 (3.7)(2), p.873.
The graph and all kernels remain those of the original input.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
open DistanceTwoRecognition ChapterB.QuasisimpleSource OriginalStar
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
include h hshort hinner

/-- Large core movement would give the original full radical opposite
image order at most 2q cubed, retaining both complete fixed cores. -/
theorem original_source_two_large_full_radical_index
    (hsy : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R = 2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z)) :
    (Q R z).relIndex (Q R t) ≤ 2 * (2^n)^3 := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hTSa : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  have hBn : Q R t ≤ normalizer ((Q R t ⊓ Ltilde R a) : Set (FreeAmalgam R)) :=
    (le_inf (Q R t).le_normalizer (hTSa.trans (original_residual_normalized a))).trans
      inf_normalizer_le_normalizer_inf
  let := finite_stabilizer R z
  let : Finite (Q R t) := Finite.of_injective
    (inclusion hTSz) (inclusion_injective _)
  let : ((Q R t ⊓ Ltilde R a).subgroupOf (Q R t)).Normal :=
    normal_subgroupOf_of_le_normalizer hBn
  let : ((Q R z).subgroupOf (Q R t)).Normal :=
    normal_subgroupOf_of_le_normalizer (hTSz.trans (Q_normalized R z))
  have hAT : Q R t ⊓ Ltilde R a ≤ Q R t := inf_le_left
  have hDT : fixedCore R a ≤ Q R t := inf_le_left.trans hQaT
  have hi := index_le_three_factors
    ((Q R t ⊓ Ltilde R a).subgroupOf (Q R t))
    ((fixedCore R a).subgroupOf (Q R t))
    ((Q R z).subgroupOf (Q R t))
  rw [←subgroupOf_sup hAT hDT,relIndex_subgroupOf hAT,relIndex_subgroupOf hDT] at hi
  change (Q R z).relIndex (Q R t) ≤
    ((Q R t ⊓ Ltilde R a) ⊔ fixedCore R a).relIndex (Q R t) *
      ((Q R z).relIndex (Q R t ⊓ Ltilde R a) *
        (Q R z).relIndex (fixedCore R a)) at hi
  have h₀ := (OriginalSylow.original_large_movement_images h hshort hinner hsy g hb path hat hzt hlarge).1
  have hD := OriginalSylow.original_source_two_large_fixedCore_actor_index h hshort hinner g hb hsy path hat hzt hlarge
  have hT := (original_component_fixedCore_relIndex h hshort hinner path.start_color hat).2
  rw [h₀] at hi
  calc
    _ ≤ ((Q R t ⊓ Ltilde R a) ⊔ fixedCore R a).relIndex (Q R t) *
        (2^n * (Q R z).relIndex (fixedCore R a)) := hi
    _ ≤ 2^n * (2^n * (2 * 2^n)) := Nat.mul_le_mul hT (Nat.mul_le_mul_left _ hD)
    _ = _ := by ring

/-- The actual original Sylow quotient excludes the large-movement branch. -/
theorem original_source_two_large_movement_false
    (hsy : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R = 2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z)) : False := by
  have hm := original_source_two_large_full_radical_index h hshort hinner hsy g hb path hat hzt hlarge
  rw [original_sylow_full_radical_card h hinner hsy path.end_color hzt] at hm
  have hq : 2 < 2^n :=
    show (2 : ℕ)^1 < 2^n from Nat.pow_lt_pow_right (by decide) h.nonbinary
  have hp : 0 < (2^n)^3 := by positivity
  have hs : 2 * (2^n)^3 < (2^n)^4 := by
    rw [pow_succ]
    nlinarith
  omega

/-- Small whole-core movement gives the midpoint center containment. -/
theorem original_source_two_of_small_core_movement
    (hsy : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R = 2)
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
  have hfull := (original_component_radical_triples h hshort hinner hsy g hb path hat hzt).2
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
/-- MS93 (3.7)(2) on the literal original Sylow input, retaining the entire
opposite core and midpoint edge center with no movement premise. -/
theorem original_source_two_midpoint_containment
    (hsy : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R = 2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    ⁅Z R z,Q R a⁆ ≤ Z R t := by
  apply original_source_two_of_small_core_movement h hshort hinner hsy g hb path hat hzt
  exact le_of_not_gt (original_source_two_large_movement_false
    h hshort hinner hsy g hb path hat hzt)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
