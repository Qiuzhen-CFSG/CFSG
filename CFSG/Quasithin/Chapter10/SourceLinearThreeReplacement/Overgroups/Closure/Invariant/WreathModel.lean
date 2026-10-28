module
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.GroupTheory.WreathTwoSylowModel
public import Mathlib.GroupTheory.PGroup

/-!
# The cubic base of the source S₃ wreath C₂ quotient

The elements whose cubes are one form the base E₉. Its centralizer is
contained in that base, so a two-subgroup acts faithfully on it. The Sylow
two-subgroups are the actual dihedral group of order eight, by transport
from the established SL₂(2) wreath model. The finite checks below concern
only permutations of three letters and the 72 elements of this quotient.

Source: Aschbacher--Smith, proof of 10.2.4, printed p.747.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Invariant.WreathModel

abbrev W := RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))

private instance : DecidableEq W :=
  (RegularWreathProduct.equivProd _ _).injective.decidableEq
private instance : Fintype W :=
  Fintype.ofEquiv _ (RegularWreathProduct.equivProd _ _).symm

private theorem cube_mul : ∀ a b : Equiv.Perm (Fin 3),
    a ^ 3 = 1 → b ^ 3 = 1 → (a * b) ^ 3 = 1 := by decide +kernel

/-- The two alternating base factors, in the literal wreath carrier. -/
def cubicBase : Subgroup W where
  carrier w := w.right = 1 ∧ ∀ i, w.left i ^ 3 = 1
  one_mem' := ⟨rfl, fun _ => one_pow 3⟩
  mul_mem' := by
    rintro a b ⟨ha, hca⟩ ⟨hb, hcb⟩
    refine ⟨by simp [ha, hb], fun i => ?_⟩
    simpa [RegularWreathProduct.mul_left, ha] using cube_mul _ _ (hca i) (hcb i)
  inv_mem' := by
    rintro a ⟨ha, hca⟩
    refine ⟨by simp [ha], fun i => ?_⟩
    simp [RegularWreathProduct.inv_left, ha, inv_pow, hca]

private instance : DecidablePred (· ∈ cubicBase) := fun _ =>
  inferInstanceAs (Decidable (_ = 1 ∧ ∀ _i, _ ^ 3 = 1))

theorem cubicBase_card : Nat.card cubicBase = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem mem_cubicBase_iff (w : W) : w ∈ cubicBase ↔ w ^ 3 = 1 := by
  exact (by decide +kernel : ∀ w : W, w ∈ cubicBase ↔ w ^ 3 = 1) w

theorem cubicBase_isPGroup : IsPGroup 3 cubicBase :=
  IsPGroup.of_card (n := 2) cubicBase_card

private def rotation : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
private def first : W := ⟨fun i => if i = 1 then rotation else 1, 1⟩
private def second : W := ⟨fun i => if i = 1 then 1 else rotation, 1⟩
private theorem first_mem : first ∈ cubicBase := by decide +kernel
private theorem second_mem : second ∈ cubicBase := by decide +kernel

/-- No nontrivial two-element centralizes the whole cubic base. -/
theorem centralizer_cubicBase_le : centralizer (cubicBase : Set W) ≤ cubicBase := by
  intro w hw
  have hc := mem_centralizer_iff.mp hw
  exact (by decide +kernel : ∀ w : W,
    first * w = w * first → second * w = w * second → w ∈ cubicBase)
      w (hc first first_mem) (hc second second_mem)

/-- The literal symmetric wreath quotient has dihedral Sylow two-subgroups. -/
theorem sylow_equiv_dihedral (S : Sylow 2 W) : Nonempty (S ≃* DihedralGroup 4) := by
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let f := RegularWreathProduct.congr e.symm (MulEquiv.refl (Multiplicative (ZMod 2)))
  let S' := S.mapSurjective (f := f.toMonoidHom) f.surjective
  obtain ⟨d⟩ := wreath_two_sylow_mulEquiv_dihedral_four S'
  exact ⟨((S : Subgroup W).equivMapOfInjective f.toMonoidHom f.injective).trans d⟩

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Invariant.WreathModel
