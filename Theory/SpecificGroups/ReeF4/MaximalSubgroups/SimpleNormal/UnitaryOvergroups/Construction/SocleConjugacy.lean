module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.UnitaryOvergroups.Construction.SocleConjugacy.Inputs
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.UnitaryOvergroups.Construction.SocleConjugacy.Descent
public import Theory.LinearAlgebra.Hermitian.ProjectivePairTransport

/-!
# Reduction of unitary socle conjugacy to split geometry and descent

Equal matrix-field and fixed-field orders identify the supplied projective
special unitary group with the fixed standard PSU model. This uses a genuine
projective matrix equivalence obtained from field transport and orthonormal
bases. Composing the supplied socle equivalence with this comparison places
it under the shared split-conjugacy contract.

A split conjugator and a right normalizer correction then give a Ree element
whose conjugation carries the exact special image of the supplied embedding
to `S.map M.subtype`. The direction and subgroup are those in
`StandardSocleConjugacy`; no marking is required to extend.

Only the conditional assembly is proved here. The split comparison and twist
correction are separate geometric obligations. Both must be discharged before
asserting the unconditional `standardSocleConjugacy` theorem. Construction of
a standard PGU embedding is not an input to these proofs, since an injective
embedding is already supplied in the target.

Source target: Malle, J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E; the PGU₃(q):2 case is reproduced in the
proof of Theorem 5 of Himstedt–Nguyen–Tiep, arXiv:0910.4758, p.3.
The reproduced list motivates the target; it is not used as a Lean theorem.
-/

public noncomputable section

namespace ReeF4.MaximalSubgroups.SimpleNormal.Construction

open Subgroup BenderSuzuki.MatrixGroups

/-- Field and form transport identify the supplied PSU with the standard
model using the exact quadratic-field and Frobenius conventions. -/
theorem nonempty_standardPSU_equiv {m : ℕ}
    {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hcard : Nat.card F = (2 ^ (2 * m + 1)) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ (2 * m + 1))) :
    Nonempty (ProjectiveSpecialUnitaryMatrixGroup J ≃* StandardPSU m) := by
  have hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ (2 * m + 1) :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 (2 * m + 1)
      (by omega) hcard hconj
  obtain ⟨f, _, hs⟩ :=
    HermitianForm.ProjectivePairTransport.exists_projective_pair_equiv_of_card
      J (standardForm m) (2 ^ (2 * m + 1)) hcard hfixed
      (standardField_card m) (standardForm_fixed_card m)
  have hmap : (ProjectiveSpecialUnitaryMatrixGroup J).map f.toMonoidHom =
      ProjectiveSpecialUnitaryMatrixGroup (standardForm m) := by
    ext x
    rw [mem_map_equiv]
    simpa only [MulEquiv.apply_symm_apply] using (hs (f.symm x)).symm
  exact ⟨(f.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)⟩

/-- Split comparison and the twist correction suffice for the full published
contract, including arbitrary Hermitian forms and the exact embedded image. -/
theorem standardSocleConjugacy_of_split_and_correction
    (hSplit : SplitSocleConjugacy) (hCorrection : SocleTwistCorrection) :
    StandardSocleConjugacy := by
  intro m hm M hM hsolv hR S hSn hSs hSa hC F _ _ J hcard hconj e j hj
  obtain ⟨f⟩ := nonempty_standardPSU_equiv J hcard hconj
  obtain ⟨x, hx⟩ := hSplit m hm M hM hsolv hR S hSn hSs hSa hC (e.trans f) j hj
  obtain ⟨c, hc, he⟩ :=
    hCorrection m hm M hM hsolv hR S hSn hSs hSa hC (e.trans f) j hj x hx
  exact conjugacy_of_split_conjugacy_and_correction
    (standardSpecialImage j) (S.map M.subtype) x c hx hc he

end ReeF4.MaximalSubgroups.SimpleNormal.Construction
