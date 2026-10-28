module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.UnitaryOvergroups.Construction.StandardModel

/-!
# Split conjugacy and descent for a Ree unitary socle

The unitary socle is first compared with the special image of the supplied
PGU embedding inside the split F4 group. A split conjugator need not be fixed
by the Ree twist. Multiplication on the right by an element of the normalizer
of the source subgroup preserves its subgroup image; the displayed
coboundary equation is precisely what makes that product fixed. This does
not require preserving the pointwise action of the split conjugator.

These are two unproved geometric obligations, not a maximal-subgroup theorem.
The second takes a split conjugator as input and can be proved independently
of its existence. The socle marking is unrestricted in both obligations.

Source target: Malle, J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E; the PGU3(q):2 case is reproduced in
Himstedt–Nguyen–Tiep, arXiv:0910.4758, proof of Theorem 5, p.3.
The split-conjugacy/descent separation here is a proof reduction, not a
statement quoted from that list.
-/

public noncomputable section

namespace ReeF4.MaximalSubgroups.SimpleNormal.Construction

open Subgroup BenderSuzuki.MatrixGroups

/-- The special projective group paired with the already published PGU model. -/
abbrev StandardPSU (m : ℕ) := ProjectiveSpecialUnitaryMatrixGroup (standardForm m)

/-- The exact special image occurring in `StandardSocleConjugacy`. -/
@[expose] def standardSpecialImage {m : ℕ} (j : StandardPGU m →* Model m) :
    Subgroup (Model m) :=
  (j.comp (projectiveSpecialInclusion (standardForm m))).range

/-- The same image in the split root-matrix group, using the actual inclusion. -/
@[expose] def splitSpecialImage {m : ℕ} (j : StandardPGU m →* Model m) :
    Subgroup (SplitGroup m) :=
  (standardSpecialImage j).map (toSplitGroup m)

/-- The geometric comparison inside split F4. The given equivalence supplies
the isomorphism type only; no pointwise extension of it is requested. -/
@[expose] def SplitSocleConjugacy : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ S : Subgroup M,
      S.Normal → IsSimpleGroup S → ¬ IsMulCommutative S →
      centralizer (S : Set M) = ⊥ → (S ≃* StandardPSU m) →
      ∀ j : StandardPGU m →* Model m, Function.Injective j →
        ∃ x : SplitGroup m,
          (splitSpecialImage j).map (MulAut.conj x).toMonoidHom =
            (S.map M.subtype).map (toSplitGroup m)

/-- Correct an already supplied split conjugator by a normalizer element.
The right-hand side is the defect of being fixed by the Ree twist. Relative
self-centralization in M does not by itself solve this equation in split F4.
A centralizer element suffices, but is not required: the socle is unmarked. -/
@[expose] def SocleTwistCorrection : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ S : Subgroup M,
      S.Normal → IsSimpleGroup S → ¬ IsMulCommutative S →
      centralizer (S : Set M) = ⊥ → (S ≃* StandardPSU m) →
      ∀ j : StandardPGU m →* Model m, Function.Injective j →
      ∀ x : SplitGroup m,
        (splitSpecialImage j).map (MulAut.conj x).toMonoidHom =
          (S.map M.subtype).map (toSplitGroup m) →
        ∃ c : SplitGroup m, c ∈ normalizer (splitSpecialImage j : Set (SplitGroup m)) ∧
          c * (reeTwist m c)⁻¹ = x⁻¹ * reeTwist m x

end ReeF4.MaximalSubgroups.SimpleNormal.Construction
