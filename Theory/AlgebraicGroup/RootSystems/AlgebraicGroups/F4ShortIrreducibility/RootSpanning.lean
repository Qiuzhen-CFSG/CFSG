module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4ShortIrreducibility.InvariantSubspaces

/-!
# Generation of the literal F4 short ideal from one root vector

An ambient coordinate submodule invariant under every actual root curve and
containing one short-root coordinate vector contains the whole short ideal.
Every short root has a simple-root route, and reversing that route returns to
a short simple root. The two short simple roots are joined by a two-reflection
word, as follows from their Cartan entries. Thus all short-root vectors follow
by the actual Tits-word action. The opposite-root equations in
`InvariantSubspaces` then supply the short Cartan coordinates.

This proves the root-vector generation step with the supplied root vector as
an explicit hypothesis. Detection of such a vector in an arbitrary nonzero
invariant subspace belongs to the irreducibility assembly.

Sources: GLS3 Remark 1.8.9 (`refs/KGroup/GLS3/Chapter1.tex`) for the Weyl
geometry, and Steinberg's integral Chevalley construction
(`refs/KGroup/GLS3/Chapter2St1.tex`) for the root and Cartan actions.
-/

public section

open scoped Classical
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ReeF4 ReeF4.WordRelations.ShortOperators

namespace Theory.AlgebraicGroup.F4Chevalley.ShortIrreducibility

private lemma reflectionWord_append (u w : List typeF4RootPairing_base.support) (r : Root) :
    reflectionWord (u ++ w) r = reflectionWord u (reflectionWord w r) := by
  induction u with
  | nil => rfl
  | cons i u ih =>
    simpa only [List.cons_append, reflectionWord] using
      congrArg (typeF4RootPairing.reflectionPerm i) ih

private lemma reflectionWord_reverse_cancel
    (w : List typeF4RootPairing_base.support) (r : Root) :
    reflectionWord w.reverse (reflectionWord w r) = r := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simpa only [List.reverse_cons, reflectionWord_append, reflectionWord,
      typeF4RootPairing.reflectionPerm_self] using ih

private lemma short_simple_bridge :
    reflectionWord [typeF4RootPairing_baseEquiv 2, typeF4RootPairing_baseEquiv 3]
        (typeF4RootPairing_baseEquiv 2 : Root) = (typeF4RootPairing_baseEquiv 3 : Root) := by
  have h23 : typeF4RootPairing.pairingIn ℤ
      (typeF4RootPairing_baseEquiv 2) (typeF4RootPairing_baseEquiv 3) = -1 := by
    change typeF4RootPairing_base.cartanMatrix
      (typeF4RootPairing_baseEquiv 2) (typeF4RootPairing_baseEquiv 3) = -1
    rw [typeF4RootPairing_base_cartan_apply]
    norm_num [typeF4CartanMatrix]
    decide
  have h32 : typeF4RootPairing.pairingIn ℤ
      (typeF4RootPairing_baseEquiv 3) (typeF4RootPairing_baseEquiv 2) = -1 := by
    change typeF4RootPairing_base.cartanMatrix
      (typeF4RootPairing_baseEquiv 3) (typeF4RootPairing_baseEquiv 2) = -1
    rw [typeF4RootPairing_base_cartan_apply]
    norm_num [typeF4CartanMatrix]
    decide
  apply typeF4RootPairing.root.injective
  simp only [reflectionWord, typeF4RootPairing.root_reflectionPerm]
  rw [RootPairing.reflection_apply_root' ℤ (i := (typeF4RootPairing_baseEquiv 3 : Root)), h23,
    neg_one_smul, sub_neg_eq_add, map_add, typeF4RootPairing.reflection_apply_self,
    RootPairing.reflection_apply_root' ℤ, h32, neg_one_smul]
  abel

private lemma short_simple_cases
    (i : typeF4RootPairing_base.support) (hi : IsShortRoot i.val) :
    i = typeF4RootPairing_baseEquiv 2 ∨ i = typeF4RootPairing_baseEquiv 3 := by
  obtain ⟨j, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
  rw [isShortRoot_simple] at hi
  have hj : j = 2 ∨ j = 3 := by omega
  rcases hj with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma short_simple_transitive (i j : typeF4RootPairing_base.support)
    (hi : IsShortRoot i.val) (hj : IsShortRoot j.val) :
    ∃ w : List typeF4RootPairing_base.support, reflectionWord w i.val = j.val := by
  rcases short_simple_cases i hi with rfl | rfl <;>
    rcases short_simple_cases j hj with rfl | rfl
  · exact ⟨[], rfl⟩
  · exact ⟨[typeF4RootPairing_baseEquiv 2, typeF4RootPairing_baseEquiv 3], short_simple_bridge⟩
  · refine ⟨[typeF4RootPairing_baseEquiv 3, typeF4RootPairing_baseEquiv 2], ?_⟩
    have h := reflectionWord_reverse_cancel
      [typeF4RootPairing_baseEquiv 2, typeF4RootPairing_baseEquiv 3]
      (typeF4RootPairing_baseEquiv 2 : Root)
    rw [short_simple_bridge] at h
    exact h
  · exact ⟨[], rfl⟩

/-- All literal short F4 roots belong to one orbit of simple reflection words. -/
private lemma exists_reflectionWord_of_short (r s : Root)
    (hr : IsShortRoot r) (hs : IsShortRoot s) :
    ∃ w : List typeF4RootPairing_base.support, reflectionWord w r = s := by
  let rr := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
  let rs := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) s
  have hr' : IsShortRoot rr.simple.val :=
    (isShortRoot_reflectionWord rr.word rr.simple.val).mp (rr.target.symm ▸ hr)
  have hs' : IsShortRoot rs.simple.val :=
    (isShortRoot_reflectionWord rs.word rs.simple.val).mp (rs.target.symm ▸ hs)
  obtain ⟨w, hw⟩ := short_simple_transitive rr.simple rs.simple hr' hs'
  refine ⟨rs.word ++ w ++ rr.word.reverse, ?_⟩
  simp only [reflectionWord_append]
  have hrrev : reflectionWord rr.word.reverse r = rr.simple.val := by
    simpa only [rr.target] using reflectionWord_reverse_cancel rr.word rr.simple.val
  rw [hrrev, hw, rs.target]

variable {k : Type*} [Field k] [IsAlgClosed k] [CharP k 2]

/-- One short-root coordinate vector generates the whole short ideal in every
ambient submodule stable under the actual root curves. -/
theorem RootCurveInvariant.shortSubmodule_le_of_root_single
    {W : Submodule k (BasisIndex → k)} (hW : RootCurveInvariant W)
    (r : Root) (hr : IsShortRoot r)
    (hmem : Pi.single (Sum.inr r : BasisIndex) (1 : k) ∈ W) :
    shortSubmodule ≤ W := by
  apply hW.shortSubmodule_le_of_root_mem
  intro s hs
  obtain ⟨w, hw⟩ := exists_reflectionWord_of_short r s hr hs
  simpa only [hw] using hW.reflectionWord_single_mem w r hmem

end Theory.AlgebraicGroup.F4Chevalley.ShortIrreducibility
