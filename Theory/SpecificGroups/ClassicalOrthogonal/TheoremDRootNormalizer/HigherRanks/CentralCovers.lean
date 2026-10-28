module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.CentralCovers.Transport

/-!
# Nonbinary even orthogonal central covers are not quasithin in higher ranks

Over a finite field of characteristic two with more than two elements,
every finite central cover of the actual plus model of rank at least three,
or minus model of rank at least four, has an odd-prime rank-three two-local
subgroup. The proof uses the literal root normalizer and squared diagonal
torus. The double flips lie in the plus elementary subgroup and in the split
commutator subgroup extended by the chosen anisotropic plane in the minus
model. Thus all root, torus, inverter and quotient-map hypotheses of the
common argument are discharged in the original carriers.

No oddness assumption on the central kernel, perfectness assumption on the
cover, or simplicity premise is used. This supplies the orthogonal model
input for Aschbacher--Smith A.2.18, printed p.40.
-/

public noncomputable section
namespace ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.CentralCovers
variable {F : Type*} [Field F] [CharP F 2] {r : ℕ}
variable [Finite F] {E : Type*} [Group E] [Finite E]

/-- Every finite central cover of the nonbinary plus model of rank at least three is excluded. -/
theorem not_quasithin_plus (hr : 3 ≤ r) (hq : 2 < Nat.card F)
    (f : E →* POmegaPlus r F) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) : ¬ IsQuasithin E := by
  let i : Fin r := ⟨0, by omega⟩
  let j : Fin r := ⟨1, by omega⟩
  have hij : i ≠ j := Fin.ne_of_val_ne (by simp [i, j])
  exact not_quasithin_of_doubleFlips (elementarySubgroup (formD r F))
    (projectiveElementaryMap (formD r F)) hij (root_mem_elementary hij)
    (diagonal_square_mem_elementary (by omega))
    (fun _ _ h => DoubleFlip.doubleFlip_mem_elementary h)
    hr (elementaryProjective_injective _) hq f hf hk

/-- Every finite central cover of the nonbinary minus model of rank at least four is excluded. -/
theorem not_quasithin_minus (hr : 4 ≤ r) (hq : 2 < Nat.card F)
    (f : E →* ClassicalGroup.POmegaMinus r F) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) : ¬ IsQuasithin E := by
  let i : Fin (r-1) := ⟨0, by omega⟩
  let j : Fin (r-1) := ⟨1, by omega⟩
  have hij : i ≠ j := Fin.ne_of_val_ne (by simp [i, j])
  exact not_quasithin_of_doubleFlips (commutator (O (r-1) F)) (minusProjectiveHom r)
    hij (root_mem_commutator hq hij) diagonal_square_mem_commutator
    (fun _ _ h => DoubleFlip.doubleFlip_mem_commutator h)
    (by omega) (minusProjectiveHom_injective r) hq f hf hk

end ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.CentralCovers
