module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.Radical.Action
public import Theory.Representation.SL3OddNaturalNormalizer.PointFixers
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The actual U* lies in the supplied special-linear layer

The faithful action of the original quotient LT/O₂(LT) becomes a binary
representation on the given natural coordinates. Normality of L* makes
each actor semilinear. Every U* actor fixes the marked nonzero F-line
pointwise, so its coefficient automorphism is trivial. Elementarity of U*
and characteristic two then give determinant one. The supplied model of
L* realizes this matrix, and faithfulness gives membership in the literal
starred L. The same argument covers n=1.

The two inputs U≤T and Φ(U)≤V₁ are precisely the earlier G.2.2 conclusions.
No radical identification or starred-generation conclusion is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, G.2.5(1),
printed p.335, with the G.2.3 argument on p.333 and G.2.2 on p.332.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree
open Setup
variable {G : Type*} [Group G] [Finite G]
variable {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : Hypothesis D F n g h)
namespace Hypothesis
include d

private def binaryStarAction [Algebra (ZMod 2) F] :
    Representation (ZMod 2) D.Star (Fin 3 → F) where
  toFun a := (AddEquiv.toMultiplicative.symm (d.starAction a)).toAddMonoidHom.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change (d.starAction 1 (Multiplicative.ofAdd v)).toAdd = v
    rw [map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    change (d.starAction (a * b) (Multiplicative.ofAdd v)).toAdd =
      (d.starAction a (d.starAction b (Multiplicative.ofAdd v))).toAdd
    rw [map_mul]
    rfl

/-- The original starred U lies in the given starred L, using only the
containment and Frattini conclusions of G.2.2. -/
theorem star_U_le_star_L (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) : D.star D.U ≤ D.star D.L := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using d.field_card)
  let : Algebra (ZMod 2) F := ZMod.algebra _ _
  let : (D.star D.L).Normal := d.star_L_normal
  let : IsElementaryAbelian 2 (D.star D.U) := d.star_U_elementary hUT hf
  have hP : d.point ≠ ⊥ := Submodule.one_le_finrank_iff.mp (by rw [d.point_dimension])
  intro u hu
  have hu2 : u ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian u hu
  obtain ⟨s, hs⟩ :=
    Representation.SL3OddNaturalNormalizer.exists_specialLinear_of_square_one_of_fixes_submodule
      (D.star D.L) d.model d.binaryStarAction
      (fun l v => d.starAction_on_L l v) d.point hP u hu2
      (fun v hv => congrArg Multiplicative.toAdd (d.starAction_U_fixes_point u hu v hv))
  have he : u = (d.model.symm s : D.Star) := by
    apply d.starAction_injective
    apply MulEquiv.ext
    intro v
    change (d.starAction u (Multiplicative.ofAdd v.toAdd)).toAdd =
      (d.starAction (d.model.symm s) (Multiplicative.ofAdd v.toAdd)).toAdd
    rw [d.starAction_on_L, d.model.apply_symm_apply]
    exact hs v.toAdd
  exact he ▸ (d.model.symm s).property

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree
