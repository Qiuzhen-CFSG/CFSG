module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.FieldClassical.Inputs
public import Theory.SpecificGroups.PSL3.FieldComponentFixer
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# The remaining embedded-component placement for the PSL₃ field row

Elementary-matrix perfectness identifies the derived PSL₃ endpoint with PSL₃
itself, including PSL₃(2). The placement contract asks for actual ambient
coordinates in which the given component contains the six root groups over
the fixed field of an involutory coefficient automorphism. It does not infer
those coordinates from the endpoint types and does not assert that the
contract has been proved.

This is the remaining placement input from the involution alternatives in
Aschbacher–Smith 16.1.4(4) and 16.1.7(3a), used in 16.3.5, printed
pp.1171–1173 and 1178–1179 of `refs/quasithin.pdf` (1 March 2004 manuscript).
-/

@[expose] public section
open scoped MatrixGroups
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.CounterexampleGeometry.CoveredPersistence
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.FieldClassical.LinearThree
universe u
/-- The derived PSL₃ endpoint is the whole PSL₃ model, including field order two.
This uses elementary-matrix perfectness, not an identification by a family tag. -/
theorem derivedAt_iff_isPSL {S : Type u} [Group S] (q : ℕ) :
    FieldFamily.linearThree.DerivedAt S q ↔ ClassicalGroup.IsPSL S 3 q := by
  constructor
  · rintro ⟨M, hM, hfin, hm, ⟨d⟩⟩
    obtain ⟨F, hF, hFfin, hq, ⟨e⟩⟩ := hm
    let := Atlas.psl_perfect (F := F) 3 (by decide)
    let : Group.IsPerfect M := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact ⟨F, hF, hFfin, hq, ⟨d.trans
      ((MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans
        (Subgroup.topEquiv.trans e))⟩⟩
  · rintro ⟨F, hF, hFfin, hq, ⟨e⟩⟩
    let := Atlas.psl_perfect (F := F) 3 (by decide)
    refine ⟨PSL(3,F), inferInstance, inferInstance,
      ⟨F, hF, hFfin, hq, ⟨MulEquiv.refl _⟩⟩, ?_⟩
    exact ⟨e.trans ((Subgroup.topEquiv.symm).trans
      (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).symm)⟩

/-- The still-unproved placement of the actual component around the fixed-field
roots. Only containment is needed for the pointwise-fixer bound. -/
def RootPlacement : Prop :=
  ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S]
    (n : ℕ), 1 ≤ n → ClassicalGroup.IsPSL S 3 (2 ^ (2 * n)) →
    ∀ (a : MulAut S), orderOf a = 2 → ∀ P : Subgroup S,
      IsComponentIn P a.fixedSubgroup → IsPGroup 2 (center P) →
      ClassicalGroup.IsPSL (P ⧸ center P) 3 (2 ^ n) →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        Nat.card F = 2 ^ (2 * n) ∧
        ∃ (e : S ≃* PSL(3,F)) (σ : F ≃+* F), orderOf σ = 2 ∧
          Matrix.PSL3.FieldComponentFixer.fieldRoots σ ≤ P.map e.toMonoidHom

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.FieldClassical.LinearThree
