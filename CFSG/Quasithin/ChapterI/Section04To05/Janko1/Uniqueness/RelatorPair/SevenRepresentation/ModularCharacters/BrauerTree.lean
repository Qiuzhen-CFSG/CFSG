module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.Exhaustion
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.LocalEleven

/-!
# Assembly of the actual characteristic-eleven family

The ten edge dimensions are distinct and disjoint from the four defect-zero
dimensions. Consequently the two actual irreducible families form fourteen
pairwise inequivalent modules. The ordinary table has fourteen eleven-regular
classes, so simple trace independence gives completeness. Reindexing by `Fin 14`
then verifies all natural dimension equations of `ElevenTreeFamily`.

This proves the assembly conditional on the two modular realization contracts.
Those contracts still require construction from the source hypotheses and
`OrdinaryData`; this module does not yet prove the source existence theorem.
Source: Janko, J. Algebra 3 (1966), 147–186; Gorenstein, *Finite Groups*, §16.6,
p.482. Numerical path provenance is recorded in `ModularCharacters/Source.md`.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree

variable {G : Type*} [Group G]

private theorem pathDegree_injective : Function.Injective pathDegree := by decide +kernel
private theorem degrees_disjoint : ∀ i j, pathDegree i ≠ defectZeroDegree j := by decide +kernel

private def sumDegree : Fin 10 ⊕ Fin 4 → ℕ := Sum.elim pathDegree defectZeroDegree

private def sumRep (p : PathModules G) (z : DefectZeroModules G) :
    ∀ i, Representation ElevenClosure G (Fin (sumDegree i) → ElevenClosure)
  | .inl i => p.rep i
  | .inr i => z.rep i

private theorem sum_inequivalent (p : PathModules G) (z : DefectZeroModules G) :
    Pairwise fun i j => IsEmpty ((sumRep p z i).Equiv (sumRep p z j)) := by
  intro i j hij
  constructor
  intro e
  have hd : sumDegree i = sumDegree j := by
    simpa only [Module.finrank_fin_fun] using e.toLinearEquiv.finrank_eq
  cases i with
  | inl i =>
    cases j with
    | inl j => exact hij (congrArg Sum.inl (pathDegree_injective hd))
    | inr j => exact degrees_disjoint i j hd
  | inr i =>
    cases j with
    | inl j => exact degrees_disjoint j i hd.symm
    | inr j => exact (z.inequivalent (fun h => hij (congrArg Sum.inr h))).false e

private theorem sum_irreducible (p : PathModules G) (z : DefectZeroModules G)
    (i : Fin 10 ⊕ Fin 4) : Representation.IsIrreducible (sumRep p z i) := by
  cases i with
  | inl i => exact p.irreducible i
  | inr i => exact z.irreducible i

variable [Finite G]

/-- Combine actual path and defect-zero realizations. The source table supplies
completeness; existence of the two realization inputs remains to be proved. -/
public def treeFamily_of_modules (d : OrdinaryData G) (p : PathModules G)
    (z : DefectZeroModules G) : ElevenTreeFamily G where
  degree i := sumDegree (finSumFinEquiv.symm i)
  rep i := sumRep p z (finSumFinEquiv.symm i)
  irreducible i := sum_irreducible p z _
  degree_equations := by decide +kernel
  complete n σ hσ := by
    have hne : Pairwise fun i j : Fin 14 =>
        IsEmpty ((sumRep p z (finSumFinEquiv.symm i)).Equiv
          (sumRep p z (finSumFinEquiv.symm j))) := by
      intro i j hij
      exact sum_inequivalent p z (fun h => hij (finSumFinEquiv.symm.injective h))
    obtain ⟨i, ⟨e⟩⟩ := d.equiv_of_fourteen_irreducibles _ _
      (fun i => sum_irreducible p z (finSumFinEquiv.symm i)) hne n σ hσ
    exact ⟨i, fun g _ => congrFun (Representation.char_iso e.symm) g⟩

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree
