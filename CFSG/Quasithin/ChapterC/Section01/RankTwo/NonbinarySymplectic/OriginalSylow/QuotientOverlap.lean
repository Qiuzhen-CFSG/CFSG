module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalSylow.SourceThree
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFixedTrivialQuotient
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic

/-!
# The original Sylow critical overlap after the whole fixed-core quotient

For every critical pair on the literal original Sylow star, the kernel of the endpoint
quotient on the product of its two center layers lies in their actual
intersection. Thus their relative index q survives that quotient. The
argument retains the complete fixed core and the literal original graph;
it applies to every homomorphism with that precise kernel.

Source: MS93 (3.7), printed pp.876–877, with its tilde quotient convention.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
open DistanceTwoRecognition OriginalStar
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
variable (hsyl : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
  (R.subgroupOf K).map (componentProjection h))
include h hshort hinner hsyl

/-- The opposite original center in the first core lies in the first center. -/
theorem original_source_critical_overlap_le_Z
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    Z R z ⊓ Q R a ≤ Z R a := by
  obtain ⟨hin,_,hX,_⟩ := original_source_three_of_full_sylow h hshort hinner hsyl g hb path hat hzt
  have hc : Z R z ⊓ Q R a ≤
      centralizer ((Z R a ⊔ Q R z : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
    apply le_centralizer_iff.mp
    apply sup_le
    · exact (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R a path.start_color)).trans (centralizer_le inf_le_right)
    · exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R z path.end_color))).trans (centralizer_le inf_le_left)
  let := g.Z_elementary (by omega : 0<g.b R) z path.end_color
  intro x hx
  rw [←hX]
  exact mem_omegaCenter_iff.mpr ⟨hx.2,
    elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx.1,
    (hc.trans (centralizer_le hin)) hx⟩

/-- The original Sylow source overlap index survives the quotient by the entire fixed core.
Its kernel on Z_a Z_z is contained in the actual overlap: its Z_a part lies
in the midpoint center. The map is arbitrary with the exact whole fixed
core as kernel, so the literal endpoint quotient is an immediate instance. -/
theorem original_source_critical_quotient_overlap
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    {J : Type*} [Group J] (f : stabilizer R a →* J)
    (hf : f.ker=(fixedCore R a).subgroupOf (stabilizer R a)) :
    ((Z R z).subgroupOf (stabilizer R a) |>.map f).relIndex
      ((Z R a).subgroupOf (stabilizer R a) |>.map f)=2^n := by
  have hZQ : Z R a ≤ Q R a :=
    (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0<g.b R; omega)).trans (omegaCenter_le _)
  have hZS : Z R a ≤ stabilizer R a := hZQ.trans (fun _ hx => hx.1)
  have hZzS : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  have hover := original_source_critical_overlap_le_Z h hshort hinner hsyl g hb path hat hzt
  have hk : ((Z R a ⊔ Z R z) ⊓ fixedCore R a) ≤
      Z R a ⊓ Z R z := by
    intro x hx
    have hn : Z R z ≤ normalizer (Z R a : Set (FreeAmalgam R)) :=
      hZzS.trans (Z_normalized R a)
    have hxprod : x ∈ Z R a ⊔ Z R z := hx.1
    rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hn] at hxprod
    obtain ⟨u,hu,v,hv,he⟩ := hxprod
    change u*v=x at he
    have hvQ : v ∈ Q R a := by
      have hh := (Q R a).mul_mem ((Q R a).inv_mem (hZQ hu)) hx.2.1
      rwa [←he,inv_mul_cancel_left] at hh
    have hxZ : x ∈ Z R a := he ▸ (Z R a).mul_mem hu (hover ⟨hv,hvQ⟩)
    have hxX : x ∈ X R a := g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; change 0<g.b R; omega) hxZ
    have hxt : x ∈ Z R t :=
      original_fixed_X_le_edge h hinner path.start_color hat ⟨hxX,hx.2.2⟩
    exact ⟨hxZ,Sp4Four.edge_Z_le_endpoint R path.end_color hzt hxt⟩
  let S := stabilizer R a
  let A := (Z R a).subgroupOf S
  let B := (Z R z).subgroupOf S
  have hk' : (A ⊔ B) ⊓ f.ker ≤ A ⊓ B := by
    rw [hf]
    intro x hx
    have hxJ : x.val ∈ Z R a ⊔ Z R z := by
      have he : A ⊔ B=(Z R a ⊔ Z R z).subgroupOf S :=
        (subgroupOf_sup hZS hZzS).symm
      have hh : x ∈ (Z R a ⊔ Z R z).subgroupOf S := he ▸ hx.1
      exact hh
    exact hk ⟨hxJ,hx.2⟩
  change (B.map f).relIndex
    (A.map f)=2^n
  rw [relIndex_map_of_kernel_in_overlap _ _ _ hk',relIndex_subgroupOf hZS]
  exact (original_source_three_of_full_sylow h hshort hinner hsyl g hb path hat hzt).2.2.2.1


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
