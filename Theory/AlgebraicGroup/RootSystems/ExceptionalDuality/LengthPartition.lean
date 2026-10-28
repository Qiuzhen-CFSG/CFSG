module

import all Theory.AlgebraicGroup.RootSystems.ExceptionalDuality.Core
public import Theory.AlgebraicGroup.RootSystems.ExceptionalDuality.B2ModelAdapter
public import Theory.AlgebraicGroup.RootSystems.ExceptionalDuality.F4ModelAdapter
public import Theory.AlgebraicGroup.RootSystems.ExceptionalDualityG2

/-!
# Exceptional root-length exhaustiveness

For a finite reduced crystallographic real root pairing whose chosen numbered
base has the classified Cartan matrix `B2`, `F4`, or `G2`, this module proves
that every root index is long or short in the directed integral-pairing sense.
This is the root-system input needed to partition exceptional root subgroups in
the graph-field automorphism construction.

The classified Cartan graph is first checked to be connected, so the chosen
base makes the pairing irreducible.  The three model adapters then supply the
length calculation: `B2` uses its four-row standard-root enumeration, `F4`
uses the checked 24-row positive-root table and invariant-form lengths, and
`G2` uses the embedded six-positive-root model.  These calculations implement
the standard two-root-length classification for the exceptional self-dual
Cartan matrices, independently of any field characteristic or algebraic-group
realization.
-/

namespace Theory.AlgebraicGroup

open StandardRootSystem

private lemma exceptionalDynkinCartan_connected
    (classification : RootClassification)
    (hExceptional : IsExceptionalDualityClassification classification)
    (i j : Fin classification.rank) :
    Relation.ReflTransGen
      (fun u v => dynkinCartanEntry classification u v ≠ 0) i j := by
  rcases hExceptional with hB | hF | hG
  · rcases classification with ⟨kind, rank⟩
    rcases hB with ⟨rfl, rfl⟩
    fin_cases i <;> fin_cases j
    · exact .refl
    · exact .single (by norm_num [dynkinCartanEntry])
    · exact .single (by norm_num [dynkinCartanEntry])
    · exact .refl
  · rcases classification with ⟨kind, rank⟩
    rcases hF with ⟨rfl, rfl⟩
    let edge := fun u v : Fin 4 =>
      dynkinCartanEntry ⟨.F4, 4⟩ u v ≠ 0
    have h01 : edge 0 1 := by norm_num [edge, dynkinCartanEntry]
    have h10 : edge 1 0 := by norm_num [edge, dynkinCartanEntry]
    have h12 : edge 1 2 := by norm_num [edge, dynkinCartanEntry, Fin.ext_iff]
    have h21 : edge 2 1 := by norm_num [edge, dynkinCartanEntry, Fin.ext_iff]
    have h23 : edge 2 3 := by norm_num [edge, dynkinCartanEntry, Fin.ext_iff]
    have h32 : edge 3 2 := by norm_num [edge, dynkinCartanEntry, Fin.ext_iff]
    have hto : ∀ k : Fin 4, Relation.ReflTransGen edge k 0 := by
      intro k
      fin_cases k
      · exact .refl
      · exact .single h10
      · exact (Relation.ReflTransGen.single h21).tail h10
      · exact ((Relation.ReflTransGen.single h32).tail h21).tail h10
    have hfrom : ∀ k : Fin 4, Relation.ReflTransGen edge 0 k := by
      intro k
      fin_cases k
      · exact .refl
      · exact .single h01
      · exact (Relation.ReflTransGen.single h01).tail h12
      · exact ((Relation.ReflTransGen.single h01).tail h12).tail h23
    exact (hto i).trans (hfrom j)
  · rcases classification with ⟨kind, rank⟩
    rcases hG with ⟨rfl, rfl⟩
    fin_cases i <;> fin_cases j
    · exact .refl
    · exact .single (by norm_num [dynkinCartanEntry])
    · exact .single (by norm_num [dynkinCartanEntry])
    · exact .refl

private theorem exceptionalRootPairing_isIrreducible
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (classification : RootClassification)
    (numbering : base.support ≃ Fin classification.rank)
    (hbase : ∀ i j, base.cartanMatrixIn ℤ i j =
      dynkinCartanEntry classification (numbering i) (numbering j))
    (hExceptional : IsExceptionalDualityClassification classification) :
    P.IsIrreducible := by
  have hrank : 0 < classification.rank := by
    rcases hExceptional with hB | hF | hG
    · exact hB.2.symm ▸ by norm_num
    · exact hF.2.symm ▸ by norm_num
    · exact hG.2.symm ▸ by norm_num
  have hsupport : base.support.Nonempty :=
    ⟨numbering.symm ⟨0, hrank⟩, (numbering.symm ⟨0, hrank⟩).property⟩
  apply isIrreducible_of_cartan_connected P base hsupport
  intro s t
  rw [← numbering.symm_apply_apply s, ← numbering.symm_apply_apply t]
  exact Relation.ReflTransGen.lift numbering.symm
    (fun i j hij => by
      change base.cartanMatrixIn ℤ (numbering.symm i) (numbering.symm j) ≠ 0
      rw [hbase]
      simpa using hij)
    _ _ (exceptionalDynkinCartan_connected classification hExceptional
      (numbering s) (numbering t))

/-- Every root of a finite reduced crystallographic real root pairing with a
numbered `B2`, `F4`, or `G2` Cartan base belongs to one of the two directed
root-length classes. -/
public theorem exceptionalRootPairing_isLong_or_isShort
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (classification : RootClassification)
    (numbering : base.support ≃ Fin classification.rank)
    (hbase : ∀ i j, base.cartanMatrixIn ℤ i j =
      dynkinCartanEntry classification (numbering i) (numbering j))
    (hExceptional : IsExceptionalDualityClassification classification)
    (α : ι) : P.IsLongIndex α ∨ P.IsShortIndex α := by
  rcases hExceptional with hB | hF | hG
  · rcases classification with ⟨kind, rank⟩
    rcases hB with ⟨rfl, rfl⟩
    let _ : P.IsIrreducible := exceptionalRootPairing_isIrreducible
      base ⟨.B, 2⟩ numbering hbase (Or.inl ⟨rfl, rfl⟩)
    apply exceptional_b2_isLongIndex_or_isShortIndex_of_cartan base numbering
    intro i j
    have h := hbase (numbering.symm i) (numbering.symm j)
    rw [RootPairing.Base.cartanMatrixIn_def (S := ℤ)] at h
    fin_cases i <;> fin_cases j <;>
      simp [dynkinCartanEntry, typeBCartanMatrix] at h ⊢
    all_goals assumption
  · rcases classification with ⟨kind, rank⟩
    rcases hF with ⟨rfl, rfl⟩
    let _ : P.IsIrreducible := exceptionalRootPairing_isIrreducible
      base ⟨.F4, 4⟩ numbering hbase (Or.inr (Or.inl ⟨rfl, rfl⟩))
    apply exceptional_f4_isLongIndex_or_isShortIndex_of_cartan base numbering
    intro i j
    have h := hbase (numbering.symm i) (numbering.symm j)
    rw [RootPairing.Base.cartanMatrixIn_def (S := ℤ)] at h
    fin_cases i <;> fin_cases j <;>
      simp [dynkinCartanEntry, typeF4CartanMatrix] at h ⊢
    all_goals assumption
  · rcases classification with ⟨kind, rank⟩
    rcases hG with ⟨rfl, rfl⟩
    let _ : P.IsIrreducible := exceptionalRootPairing_isIrreducible
      base ⟨.G2, 2⟩ numbering hbase (Or.inr (Or.inr ⟨rfl, rfl⟩))
    apply exceptional_g2_isLongIndex_or_isShortIndex_of_cartan base numbering
    intro i j
    have h := hbase (numbering.symm i) (numbering.symm j)
    rw [RootPairing.Base.cartanMatrixIn_def (S := ℤ)] at h
    fin_cases i <;> fin_cases j <;>
      simp [dynkinCartanEntry, typeG2CartanMatrix] at h ⊢
    all_goals assumption

end Theory.AlgebraicGroup
