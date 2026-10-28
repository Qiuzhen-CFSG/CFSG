module

public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerMathieu
public import Theory.Mathieu.M22.Properties.MarkedA5Fixer

/-!
# The literally marked M22 branch of the A5 point-centralizer calculation

The literal local E16:A5 image has no nontrivial pointwise fixer of square
one, by the native hexacode calculation and Sylow restriction in its
normalizer.
Faithfulness on the central quotient gives the result for the original perfect
component, including the central triple cover. The explicit marking input is the actual source A.3.14 embedding.

Source: Aschbacher--Smith 10.2.9, pp.750--751; A.3.14, pp.48--49.
-/

public section
open Subgroup Theory.GroupTheory
open Sporadic.Mathieu MathieuCode Sporadic.Mathieu.M22ChapterH
namespace CFSG.Quasithin.Chapter10
variable {G : Type*} [Group G] {L I U : Subgroup G}

/-- The marked M22 and 3.M22 calculation, with the genuine central quotient
and actual normalizer action of the original subgroup U. -/
theorem source_a5_m22_marked_component_centralized
    [Group.IsPerfect I] (eI : I ⧸ center I ≃* M22)
    (hmark : Quintet.naturalActor.map M22Quintet.Q.subtype ≤
      (((L.subgroupOf I).map (QuotientGroup.mk' (center I))).map
        eI.toMonoidHom).map m22ToPairStabilizer)
    [IsElementaryAbelian 2 U]
    (hUN : U ≤ normalizer (I : Set G)) (hUL : U ≤ centralizer (L : Set G)) :
    U ≤ centralizer (I : Set G) := by
  intro u hu
  let n : normalizer (I : Set G) := ⟨u,hUN hu⟩
  let a : MulAut I := I.normalizerMonoidHom n
  have hn : n ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian u hu)
  have ha : a ^ 2 = 1 := by
    change (I.normalizerMonoidHom n) ^ 2 = 1
    rw [←map_pow,hn,map_one]
  have hf : ∀ l ∈ L.subgroupOf I, a l = l := by
    intro l hl
    apply Subtype.ext
    change u * l.val * u⁻¹ = l.val
    exact mul_inv_eq_iff_eq_mul.mpr ((hUL hu l.val hl).symm)
  have he := m22_perfect_cover_marked_involutory_fixer_eq_one
    eI (L.subgroupOf I) hmark a ha hf
  intro i hi
  have hh := congrArg (fun f : MulAut I => (f ⟨i,hi⟩ : G)) he
  change u * i * u⁻¹ = i at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The source point centralizer supplies the original U normalizer condition.
The same literal embedding marking is retained for the two Mathieu central covers. -/
theorem source_a5_m22_marked_point_component_centralized
    [Group.IsPerfect I] (eI : I ⧸ center I ≃* M22)
    (hmark : Quintet.naturalActor.map M22Quintet.Q.subtype ≤
      (((L.subgroupOf I).map (QuotientGroup.mk' (center I))).map
        eI.toMonoidHom).map m22ToPairStabilizer)
    [IsElementaryAbelian 2 U]
    (v : G) (hUv : U ≤ centralizer ({v} : Set G))
    (hIN : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (hUL : U ≤ centralizer (L : Set G)) : U ≤ centralizer (I : Set G) :=
  source_a5_m22_marked_component_centralized eI hmark (hUv.trans hIN) hUL

end CFSG.Quasithin.Chapter10
