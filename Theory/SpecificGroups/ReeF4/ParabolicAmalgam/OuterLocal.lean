module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.FieldAction
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.Residual
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.PerfectSeeds
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.BinaryAutomorphisms
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms

/-!
# Local residuals and two-power automorphisms of the Ree groups

For `m ≥ 1`, both concrete fixed seeds are perfect and equal their solvable
residuals. The Suzuki proof combines its actual Levi projection with radical
containment in the derived subgroup; the linear proof reuses the existing
commutator-generation result. The independent root geometry identifies these
seeds with the embedded O^{2′} of the published parabolics, giving the local
factor equality used by the source.

Every two-power-order automorphism of `Model m` is inner. For `m ≥ 1`, the
proved local-action coverage and odd field period give this restriction.
At `m = 0`, the actual derived-group comparison and bijective conjugation
action identify the full Ree carrier with the automorphism group of Parrott's
Tits group. Its proved automorphism-tower theorem gives innerness even without
the two-power assumption. No odd-order assertion is made about the Tits
group's outer automorphism group.

These are the local residual and automorphism inputs for Aschbacher–Smith
F.1.12, printed pp.263–264 of `refs/quasithin.pdf`. They have no additional
projection, simplicity, generation or automorphism-coverage hypotheses.
The source's extension elimination and complete amalgam classification are
assembled by the parent development.
-/

public section

namespace ReeF4.Parabolics.OuterLocal

/-- Every two-power-order automorphism of the concrete Ree carrier is inner,
including the full binary Ree group at `m = 0`. -/
theorem inner_of_twoPower (m : ℕ) (α : MulAut (Model m)) (n : ℕ)
    (hpow : α ^ (2 ^ n) = 1) : ∃ g : Model m, MulAut.conj g = α := by
  cases m with
  | zero => exact binary_inner_of_twoPower α n hpow
  | succ m =>
    exact LargeAutomorphisms.inner_of_twoPower (Nat.succ_le_succ (Nat.zero_le m)) α n hpow

end ReeF4.Parabolics.OuterLocal
