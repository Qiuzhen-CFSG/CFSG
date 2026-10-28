module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuTwentyTwo.Reduction
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuTwentyTwo.HexadLocals
public import Theory.Mathieu.M22.Properties.HexadMaximal

/-!
# The concrete M₂₂ component intersection

The inner involution projection, its fixed hexad, and the actual component
Sylow subgroup are constructed from the source inputs. The reduction uses
the literal block decomposition to force a suitable hexad local overgroup
into M, then uses ordinary maximality to identify the intersection.

The local-overgroup construction handles the full S-orbit of the component;
only N_S(L) is required to preserve its hexad subgroup. Its alternating-power
extension excludes the allowed subnormal blocks. Combining this construction
with ordinary hexad maximality discharges both premises of the reduction.
The actual hexad kernel and quotient then give the source E₁₆-by-A₆ extension
for the intersection.

This proves the direct M₂₂-model case from LocalSetup and the literal inner
action in 1.1.5(3)(f). Elimination of central covers is a separate argument.

Source: Aschbacher–Smith 2.3.9(7)(f), printed pp.525–526.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Sporadic.Mathieu Theory.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G]

/-- The direct M₂₂ intersection calculation in 2.3.9(7)(f), with the actual
model isomorphism and inner action from 1.1.5(3)(f). Both the local block
calculation and ordinary hexad maximality are discharged. -/
theorem mathieuTwentyTwo_intersection
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M22)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range) :
    ∃ B ∈ m22Blocks,
      (M.subgroupOf L).map e.toMonoidHom = MulAction.stabilizer M22 B :=
  mathieuTwentyTwo_intersection_of_hexadMaximality h e α hα hinner
    m22_hexad_stabilizer_isCoatom

/-- The source A₆/E₁₆ conclusion for the actual component intersection:
a normal elementary abelian subgroup of order sixteen with quotient A₆. -/
theorem mathieuTwentyTwo_extension
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M22)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range) :
    AlternatingBySixteen (M.subgroupOf L) 6 := by
  obtain ⟨B, hB, heq⟩ := mathieuTwentyTwo_intersection h e α hα hinner
  let eq : M.subgroupOf L ≃* MulAction.stabilizer M22 B :=
    (e.subgroupMap (M.subgroupOf L)).trans (MulEquiv.subgroupCongr heq)
  exact (m22Hexad_extension hB).of_equiv eq.symm

end CFSG.Quasithin.Chapter2.ComponentRefinement

end
