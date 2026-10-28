module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceB513.SplitModels

/-!
# The reducible source branches of the B.5.13 dual bound

The moved module splits from the fixed vectors in each of the three
reducible B.5.1 rows. The doubled linear-three and repeated binary natural
modules have the same quadratic ratio as their duals, using a common graph
twist; the natural-plus-dual module is self-dual. Restricting an FF offender
to the moved module bounds this common ratio by one. Fixed vectors add no
displacement, so the bound extends to the full dual.

The argument is first proved for an arbitrary representation. Evaluation
then supplies the literal-dual applications without expanding subtype dual
coordinates throughout the model proof.

Source: Aschbacher–Smith B.5.13, printed p.111, using B.5.1(1)(ii)–(iv)
and the splitting conclusions of B.5.1(4).
-/

public section

open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.ChapterB.SourceB513
open QuasisimpleSource QuasisimpleSource.ExtensionConsequences
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (π : Representation (ZMod 2) G V) {L : Subgroup G}

/-- Two copies of the linear-three natural module give the bound on the full dual. -/
theorem doubleThree_bound_on_dual (s : MovedSection π L)
    (hff : IsFFModule π) (F : BinaryField) (hL : L = ⊤)
    (e : ActionEquiv (s.space.toRepresentation.comp L.subtype)
      (repeated (linearNatural F 3) 2)) : quadraticRatio π.dual ≤ 2 := by
  have hc := doubleThree_isCompl s F hL hff e
  apply dual_quadraticRatio_le_two_of_fixed_supplement π s.space hc.sup_eq_top
  let f := ((MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv).symm
  let a : ActionEquiv s.space.toRepresentation (repeated (linearNatural F 3) 2) :=
    ⟨f.trans e.groupEquiv,e.linearEquiv,fun g v => e.intertwines (f g) v⟩
  exact dual_bound_of_marked_ratio a (doubledThree_dual_ratio F)
    (FF_subrepresentation s.space hff)

/-- A natural-plus-dual moved module gives the bound on the full dual. -/
theorem naturalDual_bound_on_dual (s : MovedSection π L)
    (hff : IsFFModule π) {d : ℕ} (hd : 4 ≤ d) (hL : L = ⊤)
    (hn : IsNaturalPlusDual (s.space.toRepresentation.comp L.subtype) d) :
    quadraticRatio π.dual ≤ 2 := by
  have hc := naturalDual_isCompl s hd hL hn
  obtain ⟨e⟩ := hn
  apply dual_quadraticRatio_le_two_of_fixed_supplement π s.space hc.sup_eq_top
  let f := ((MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv).symm
  let a : ActionEquiv s.space.toRepresentation (naturalPlusDual d) :=
    ⟨f.trans e.groupEquiv,e.linearEquiv,fun g v => e.intertwines (f g) v⟩
  exact dual_bound_of_marked_ratio a (naturalPlusDual_dual_ratio d)
    (FF_subrepresentation s.space hff)

/-- A repeated binary natural moved module gives the bound on the full dual. -/
theorem repeatedNatural_bound_on_dual (s : MovedSection π L)
    (hff : IsFFModule π) {d r : ℕ} (hd : 4 ≤ d) (hL : L = ⊤)
    (hn : IsRepeatedLinearNatural (s.space.toRepresentation.comp L.subtype)
      BinaryField.two d r) : quadraticRatio π.dual ≤ 2 := by
  have hc := repeated_binary_isCompl s hd hL hn
  obtain ⟨e⟩ := hn
  apply dual_quadraticRatio_le_two_of_fixed_supplement π s.space hc.sup_eq_top
  let f := ((MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv).symm
  let a : ActionEquiv s.space.toRepresentation (repeated (linearNatural BinaryField.two d) r) :=
    ⟨f.trans e.groupEquiv,e.linearEquiv,fun g v => e.intertwines (f g) v⟩
  exact dual_bound_of_marked_ratio a (repeatedBinary_dual_ratio d r)
    (FF_subrepresentation s.space hff)

omit [Finite G] in
private theorem bound_of_bidual (hq : quadraticRatio π.dual.dual ≤ 2) :
    quadraticRatio π ≤ 2 := by
  let e : ActionEquiv π π.dual.dual :=
    { groupEquiv := MulEquiv.refl G
      linearEquiv := Module.evalEquiv (ZMod 2) V
      intertwines := by
        intro g v
        ext f
        change f (π g v) = f (π (g⁻¹)⁻¹ v)
        rw [inv_inv] }
  rwa [e.quadraticRatio_eq]

/-- The doubled-three source case on the literal dual of the original representation. -/
theorem doubleThree_dual_bound (s : MovedSection π.dual L)
    (hff : IsFFModule π.dual) (F : BinaryField) (hL : L = ⊤)
    (e : ActionEquiv (D := L) (V := s.space.toSubmodule) (s.space.toRepresentation.comp L.subtype)
      (repeated (linearNatural F 3) 2)) : quadraticRatio π ≤ 2 := by
  exact bound_of_bidual π (doubleThree_bound_on_dual π.dual s hff F hL e)

/-- The natural-plus-dual source case on the literal dual. -/
theorem naturalDual_dual_bound (s : MovedSection π.dual L)
    (hff : IsFFModule π.dual) {d : ℕ} (hd : 4 ≤ d) (hL : L = ⊤)
    (hn : IsNaturalPlusDual (D := L) (V := s.space.toSubmodule) (s.space.toRepresentation.comp L.subtype) d) :
    quadraticRatio π ≤ 2 := by
  exact bound_of_bidual π (naturalDual_bound_on_dual π.dual s hff hd hL hn)

/-- The repeated-natural source case on the literal dual. -/
theorem repeatedNatural_dual_bound (s : MovedSection π.dual L)
    (hff : IsFFModule π.dual) {d r : ℕ} (hd : 4 ≤ d) (hL : L = ⊤)
    (hn : IsRepeatedLinearNatural (D := L) (V := s.space.toSubmodule) (s.space.toRepresentation.comp L.subtype)
      BinaryField.two d r) : quadraticRatio π ≤ 2 := by
  exact bound_of_bidual π (repeatedNatural_bound_on_dual π.dual s hff hd hL hn)

end CFSG.Quasithin.ChapterB.SourceB513
