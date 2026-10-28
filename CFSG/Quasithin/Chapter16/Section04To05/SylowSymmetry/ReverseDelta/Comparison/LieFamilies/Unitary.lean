module

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Actions
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import Theory.SpecificGroups.PSL2.TwoResidual

/-!
# The unitary rank-one comparison

The consumed clauses of 16.1.4 are stated on the actual projective unitary
matrix carrier: an inner involution has its fixed subgroup in a rank-one
parabolic, and an outer involution has two-residual PSL₂(q)′. The parabolic
is the normalizer of an actual Sylow two-subgroup. The matrix field has
order q², and its involution is the specified q-power Frobenius.

The comparison itself is proved here. The concrete Sylow-normalizer theorem
makes the inner fixed subgroup solvable. A transvection calculation makes
PSL₂(q) perfect and nonsolvable for q ≥ 4. Solvability passes through both
central covering kernels, contradicting the actual residual containment.
No identification of the two components' central images is made.

`UnitaryInvolutionTable` is an explicit earlier-table input, not a proved
classification of automorphisms. Its two clauses are precisely the geometric
and residual information used here; it contains no comparison conclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.3 and 16.1.4(1),(6), printed p.1171; 16.4.11(2), printed p.1193.
-/

public section

namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups LiePreliminaries

/-- The two consumed unitary rows, with actual actions, parabolics and residuals. -/
structure UnitaryInvolutionRows {F : Type*} [Field F] (J : HermitianForm 3 F)
    (n : ℕ) : Prop where
  inner_parabolic : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
    orderOf a = 2 → (∃ x, a = MulAut.conj x) →
      ∃ P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
        a.fixedSubgroup ≤ normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))
  outer_graph : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
    orderOf a = 2 → (¬ ∃ x, a = MulAut.conj x) →
      Nonempty (pResidual 2 a.fixedSubgroup ≃* commutator (PSL2BinaryMatrixGroup n))

/-- The earlier table at every field witness in the unitary Bender range.
The assembly owner must supply these model statements. -/
@[expose] def UnitaryInvolutionTable : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F)
    (n : ℕ), 2 ≤ n → Nat.card F = (2 ^ n) ^ 2 →
    (∀ x, J.conj x = x ^ (2 ^ n)) → UnitaryInvolutionRows J n

private theorem binary_commutator_not_solvable {n : ℕ} (hn : 2 ≤ n) :
    ¬ Group.IsSolvable (commutator (PSL2BinaryMatrixGroup n)) := by
  obtain ⟨x, hx, hx1⟩ := BenderSuzuki.Converse.exists_ne_zero_ne_one n hn
  have hc : commutator (PSL2BinaryMatrixGroup n) = ⊤ :=
    SL2Simple.PSL_commutator_eq_top ⟨x, hx, fun hs => by
      rcases sq_eq_one_iff.mp hs with hs | hs
      · exact hx1 hs
      · exact hx1 (by simpa only [CharTwo.neg_eq] using hs)⟩
  let : Group.IsPerfect (PSL2BinaryMatrixGroup n) := ⟨hc⟩
  intro h
  let := h
  let e : commutator (PSL2BinaryMatrixGroup n) ≃* PSL2BinaryMatrixGroup n :=
    (MulEquiv.subgroupCongr hc).trans Subgroup.topEquiv
  exact Group.IsPerfect.not_isSolvable (PSL2BinaryMatrixGroup n)
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The unitary comparison on a specified matrix-field model, conditional
only on the displayed earlier involution rows. -/
theorem not_unitary_model (d : Contrary T z L g R r)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (e : (L ⧸ pCore 2 L) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (rows : UnitaryInvolutionRows J n) : False := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let c := (centerQuotientEquivTwoCore (component_oddCore d)).trans e
  obtain ⟨P, hP⟩ := rows.inner_parabolic (innerAction d c)
    (innerAction_order d c) (innerAction_inner d c)
  let := (CFSG.Quasithin.ChapterF.Source.rankOneSylowFacts_psu3 J n (by omega)
    hcard hconj P).solvable
  have hi : Group.IsSolvable (innerAction d c).fixedSubgroup :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hP)
  obtain ⟨efix⟩ := rows.outer_graph (outerAction d c)
    (outerAction_order d c) (outerAction_outer d c)
  apply false_of_solvable_inner_nonsolvable_outer d c hi
  intro ho
  let := ho
  exact binary_commutator_not_solvable hn
    (Group.isSolvable_of_surjective (f := efix.toMonoidHom) efix.surjective)

/-- The unitary Bender alternative, retaining its exact field witness. -/
theorem not_psu_three_quotient (d : Contrary T z L g R r)
    (rows : UnitaryInvolutionTable) {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSU (L ⧸ pCore 2 L) 3 (2 ^ n)) : False := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  exact not_unitary_model d J n hn hcard hconj e (rows F J n hn hcard hconj)

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
