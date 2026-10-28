module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.KernelSource

/-!
# Literal relative-index calculations for the large-distance contradiction

The radius quotient factors through intersection with a second kernel. A
quotient larger than16 forces one factor larger than4. Full vertex-center
intersections give the corresponding upper index bound, and the genuine
strict moving index excludes containment of a selected small kernel in B.
All indices belong to the original infinite amalgam's finite subgroups.

Source: MS93 (5.10)--(5.11), printed pp923--924. These calculations do not
establish the source's >16 radius bound or its final distance conclusion.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} (geometry : Geometry R)

private theorem radius_finite (hb : 2 < geometry.b R)
    {e : Vertex R} (he : color R e = false) : Finite (V R e) := by
  let := finite_stabilizer R e
  exact Finite.of_injective
    (inclusion ((geometry.V_le_Q hb e he).trans (fun _ hx => hx.1)))
    (inclusion_injective _)

/-- The source's final two-stage index split. No containment between the two
whole neighborhood kernels is assumed. -/
theorem radius_index_split (hb : 2 < geometry.b R)
    {e a c : Vertex R} (he : color R e = false)
    (hlarge : 16 < (Q R a).relIndex (V R e)) :
    4 < (Q R c).relIndex (V R e) ∨
      4 < (Q R a).relIndex (V R e ⊓ Q R c) := by
  let := radius_finite geometry hb he
  have hmon : (Q R a).relIndex (V R e) ≤
      (Q R a ⊓ Q R c).relIndex (V R e) :=
    relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
  have hprod := relIndex_inf_mul_relIndex (Q R a) (Q R c) (V R e)
  rw [inf_comm (Q R c) (V R e)] at hprod
  by_contra! h
  have hm := Nat.mul_le_mul h.2 h.1
  rw [hprod] at hm
  omega

/-- Once the first quotient has size at most q=4, a radius quotient larger
than q² forces the kernel quotient to be larger than q. -/
theorem radius_intersection_index_gt_four (hb : 2 < geometry.b R)
    {e a c : Vertex R} (he : color R e = false)
    (hlarge : 16 < (Q R a).relIndex (V R e))
    (hsmall : (Q R c).relIndex (V R e) ≤ 4) :
    4 < (Q R a).relIndex (V R e ⊓ Q R c) := by
  rcases radius_index_split geometry hb (c := c) he hlarge with h | h
  · omega
  · exact h

/-- The complete central intersection controls its relative index. The
central attachment is retained as the literal full vertex center. -/
theorem central_index_le_seed_index
    {a c e : Vertex R} (H : Subgroup (FreeAmalgam R)) (hHe : H ≤ Z R e)
    (hcent : H ⊓ Z R c ≤
      stabilizer R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R))) :
    (stabilizer R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R))).relIndex H ≤
      (Z R c).relIndex H := by
  let := finite_Z R e
  let : Finite H := Finite.of_injective (inclusion hHe) (inclusion_injective _)
  have hi := relIndex_le_of_le_left hcent (L := H) index_ne_zero_of_finite
  simpa only [inf_relIndex_left] using hi

/-- The source (5.9) strict moving index rules out the selected Z-kernel
being contained in B when its quotient has order at most four. -/
theorem selected_kernel_not_le_B
    {a d c : Vertex R}
    (hsmall : (Q R c).relIndex (Z R d) ≤ 4)
    (hmove : 4 < (B R a (geometry.Z_normal a)).relIndex (U R d)) :
    ¬ Z R d ⊓ Q R c ≤ B R a (geometry.Z_normal a) := by
  intro hk
  let := finite_Z R d
  let : Finite (U R d) := Finite.of_injective
    (inclusion (U_le_Z d)) (inclusion_injective _)
  have hZ : (B R a (geometry.Z_normal a)).relIndex (Z R d) ≤ 4 := by
    apply le_trans (relIndex_le_of_le_left hk index_ne_zero_of_finite)
    simpa only [inf_relIndex_left] using hsmall
  have hU := (B R a (geometry.Z_normal a)).relIndex_le_of_le_right
    (U_le_Z d) index_ne_zero_of_finite
  omega

end CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
