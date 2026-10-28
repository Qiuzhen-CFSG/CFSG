module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.SplitNormalForm.Inputs

/-!
# Root signs for concrete D4 cell exchange

A numbered simple reflection preserves every positive root except its own
simple root. Every word in the actual root reflections commutes with negation.
These two facts give the positive root on the right in both branches of the
rank-one exchange calculation, without enumerating the Weyl group or assuming
a Tits system.

Source: the root-system argument in GLS3 2.3.7–8 and §2.4
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.Standard.ConcreteBruhat.SplitNormalForm.CellCollection
open PositiveCoordinates
noncomputable section
abbrev negativeIndex (r : TypeDRootIndex 4) : TypeDRootIndex 4 :=
  (typeDRootPairing 2).reflectionPerm r r

theorem root_negativeIndex (r : TypeDRootIndex 4) :
    (typeDRootPairing 2).root (negativeIndex r) = -(typeDRootPairing 2).root r :=
  (typeDRootPairing 2).root_eq_neg_iff.mpr rfl

@[simp] theorem simple_inv (i : Fin 4) :
    (rootWeylGenerator i)⁻¹ = rootWeylGenerator i := by
  apply Subtype.ext
  exact (typeDRootPairing 2).reflectionPerm_inv _

@[simp] theorem simple_negates (i : Fin 4) :
    (rootWeylGenerator i).val (typeDSimpleRootIndex 2 i) =
      negativeIndex (typeDSimpleRootIndex 2 i) := rfl

theorem weyl_neg (w : rootWeylGroup) (r : TypeDRootIndex 4) :
    w.val (negativeIndex r) = negativeIndex (w.val r) := by
  rcases w with ⟨w, hw⟩
  induction hw using Subgroup.closure_induction generalizing r with
  | mem f hf =>
    obtain ⟨i, rfl⟩ := hf
    apply (typeDRootPairing 2).root.injective
    change (typeDRootPairing 2).root ((typeDRootPairing 2).reflectionPerm _ (negativeIndex r)) =
      (typeDRootPairing 2).root (negativeIndex ((typeDRootPairing 2).reflectionPerm _ r))
    rw [root_negativeIndex, RootPairing.root_reflectionPerm, root_negativeIndex,
      map_neg, RootPairing.root_reflectionPerm]
  | one => rfl
  | mul f g _ _ hf hg =>
    change f (g (negativeIndex r)) = negativeIndex (f (g r))
    rw [hg, hf]
  | inv f _ hf =>
    apply f.injective
    change f (f.symm (negativeIndex r)) = f (negativeIndex (f.symm r))
    rw [Equiv.apply_symm_apply, hf, Equiv.apply_symm_apply]

theorem simple_preserves_other_positive (i : Fin 4) (j : Fin 12)
    (hji : j ≠ simplePosition i) :
    (typeDRootPairing_base 2).IsPos ((rootWeylGenerator i).val (rootIndex j)) := by
  apply (rootIndex_positive j).reflectionPerm (typeDRootPairing_baseEquiv 2 i).property
  intro heq
  apply hji
  exact rootIndex_injective (heq.trans (rootIndex_simple i).symm)

theorem inverse_negative_simple_positive (w : rootWeylGroup) (i : Fin 4)
    (h : ¬ (typeDRootPairing_base 2).IsPos ((w⁻¹).val (typeDSimpleRootIndex 2 i))) :
    (typeDRootPairing_base 2).IsPos ((w⁻¹).val (negativeIndex (typeDSimpleRootIndex 2 i))) := by
  rw [weyl_neg]
  exact (RootPairing.Base.IsPos.neg_iff_not (b := typeDRootPairing_base 2) _).mpr h

end
end Triality.Standard.ConcreteBruhat.SplitNormalForm.CellCollection
