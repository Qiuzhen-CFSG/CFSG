module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.CriticalSelection.Path
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.CriticalSelection.Orientation
/-!
# The original selected critical path in Notation14.7.1

The genuine F.8 construction supplies a raw path in the original LT/H coset
graph, including its first edge and H rechoice. The actual five-point natural
section and the original point-commutator identity then supply escape and
choose an orientation with positive comparison ranks. The final theorem feeds
that constructed selection into the original14.7.69 order-two/full-image
reduction, retaining its literal star map and the genuine earlier quotient
and Sylow facts. No path, actor escape, or rank-selection premise remains.
Source: Aschbacher–Smith14.5.18(4–5),14.5.21(2),Notation14.7.1 and14.7.69,
printed pp.1018–1019,1043,1072.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
variable (d : Data T L V F W)

include d in
/-- The actual source Data constructs its selected path and both rank clauses. -/
theorem exists_selected_criticalPath
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Chapter12.Section08.Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (hUQ : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1) :
    ∃ c : CriticalPath (L:=L) F, c.RankSelection := by
  obtain ⟨c⟩ := CriticalSelection.exists_criticalPath d structural uniqueness
  exact d.select_critical_orientation structural hUQ c

include d in
/-- The original order-two/full-image reduction consumes the constructed path,
with its same intrinsic intersection and original quotient map. -/
theorem exists_order_two_or_full_criticalPath
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Chapter12.Section08.Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (hUQ : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (himage : star F (Q T L) = star F (F.Ri L 1))
    (hsylow : Chapter1.IsSylowIn 2 (star F (F.Ri L 1)) (star F (K F))) :
    ∃ c : CriticalPath (L:=L) F, c.EarlierImages ∧ c.RankSelection ∧
      (Nat.card (star F c.Uα) = 2 ∨ star F c.Uα = star F (Q T L)) := by
  obtain ⟨c,hs⟩ := d.exists_selected_criticalPath structural uniqueness hUQ
  have he := d.source_earlierImages structural c himage hsylow
  exact ⟨c,he,hs,c.order_two_or_full d he hs⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
