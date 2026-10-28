module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuTwentyTwo.HexadLocals.Transport
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuTwentyTwo.HexadLocals.BlockExclusion
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuTwentyTwo.HexadLocals.ComponentOrbit
public import Theory.Mathieu.M22.Properties.FixedHexadLocal
public import Theory.Mathieu.M22.Properties.HexadExtension

/-!
# Assembly of the M₂₂ hexad local witness

Take the join of the entire transported fixed-hexad stabilizer with the
supplied Sylow subgroup S. The geometric containments and the passage
from He to HeOver are proved in `Transport`. An alternating-power normal section
excludes all subnormal chi-zero blocks by `BlockExclusion`, including
those moved by J(S).

The component-orbit calculation establishes characteristic two and the
normal section for this join. Its intrinsic inputs are the proved
self-centralizing hexad core, invariance under every abstract automorphism
fixing the projected involution, and the genuine E₁₆-by-A₆ extension.
Only N_S(L) must preserve the hexad factor; S may permute the components.

The resulting witness discharges the local premise in the intersection
reduction. Its application below retains only ordinary hexad maximality,
whose independent assembly belongs to the intersection owner.

Source: Aschbacher–Smith, 1.1.5(3)(f), 2.3.8(4), and 2.3.9(7)(f), combined
manuscript of 1 March 2004, printed pp.502, 523, and 525–526.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Sporadic.Mathieu Theory.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G]

/-- Conditional local-witness assembly. The two structural premises concern
the actual join with the full S and must be discharged by the orbit calculation. -/
theorem mathieuTwentyTwo_hexadLocals_of_overgroup_shape
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M22) (t : L)
    (he : mathieuTwentyTwoHexadOvergroup ((S : Subgroup H).map H.subtype) e t ∈
      Chapter1.He G)
    (hshape : AlternatingPowerTwoExtension
      (mathieuTwentyTwoHexadOvergroup ((S : Subgroup H).map H.subtype) e t) 6) :
    ∃ d : MathieuTwentyTwoHexadLocal L ((S : Subgroup H).map H.subtype) e t,
      BlockObstruction M ((S : Subgroup H).map H.subtype) d.localGroup := by
  let d : MathieuTwentyTwoHexadLocal L ((S : Subgroup H).map H.subtype) e t :=
    { localGroup := mathieuTwentyTwoHexadOvergroup ((S : Subgroup H).map H.subtype) e t
      within := mathieuTwentyTwoHexadOvergroup_le _ e t
      even := mathieuTwentyTwoHexadOvergroup_mem_HeOver h e t he
      contains := le_sup_left }
  exact ⟨d, blockObstruction_of_a6PowerTwoExtension M _ _ hshape⟩

/-- The actual fixed-hexad local overgroup and its obstruction to all allowed
subnormal blocks. All intrinsic and component-orbit premises are discharged. -/
theorem mathieuTwentyTwo_hexadLocals
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M22) (t : L)
    (ht : IsConjugationProjection L z t) (ht2 : orderOf t = 2) :
    ∃ d : MathieuTwentyTwoHexadLocal L ((S : Subgroup H).map H.subtype) e t,
      BlockObstruction M ((S : Subgroup H).map H.subtype) d.localGroup := by
  have hu : orderOf (e t) = 2 := by simpa using ht2
  have hext := mathieuTwentyTwo_hexad_extension e t ht2
    (fun _ hB => m22Hexad_extension hB)
  have hc := mathieuTwentyTwo_hexad_characteristicTwo e t
    (m22FixedPoints_stabilizer_core_selfCentralizing (e t) hu)
  have hinv := mathieuTwentyTwo_hexad_normalized h e ht
    (m22FixedPoints_stabilizer_map (e t) hu)
  obtain ⟨he, hshape⟩ := mathieuTwentyTwo_hexadOvergroup_structure h e t hext hc hinv
  exact mathieuTwentyTwo_hexadLocals_of_overgroup_shape h e t he hshape

/-- Apply the constructed witness to the literal component intersection.
Only the independently owned ordinary maximality of hexad stabilizers remains. -/
theorem mathieuTwentyTwo_intersection_of_hexadMaximality
    {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z) (e : L ≃* M22)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range)
    (hmax : ∀ B ∈ m22Blocks, IsCoatom (MulAction.stabilizer M22 B)) :
    ∃ B ∈ m22Blocks,
      (M.subgroupOf L).map e.toMonoidHom = MulAction.stabilizer M22 B :=
  mathieuTwentyTwo_intersection_of_hexadLocals h e α hα hinner hmax
    (mathieuTwentyTwo_hexadLocals h e)

end CFSG.Quasithin.Chapter2.ComponentRefinement

end
