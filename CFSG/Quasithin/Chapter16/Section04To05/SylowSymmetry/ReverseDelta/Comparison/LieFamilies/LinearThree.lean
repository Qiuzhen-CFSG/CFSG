module

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Actions
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.Divisibility
public import Theory.SpecificGroups.PSL3Even.ResidualComparison

/-!
# Excluding binary PSL₃ residual pairs

The inner involution fixes a solvable root centralizer. Field, graph, and
larger graph-field outer residuals are nonsolvable, contradicting the actual
containment of the outer residual in the inner one. At the small graph
endpoint PSL₂(2)′ and the graph-field E₉ endpoint for PSL₃(4), the outer
residual has an odd divisor absent from the inner centralizer.

The central-image maps have central two-group kernels. Solvability and odd
prime divisors therefore pass through both maps without identifying the two
component centers. In particular the PSL₃(4) covers remain included. Only
containment is needed here; the stronger relative normality supplied by
`Contrary.residual_normal` is not replaced by ambient normality.

The inner-root clause is proved from the concrete matrix model. The sole
remaining earlier-table input is `LinearThreeInvolutionTable`: coverage of
outer involutory actions by the field PSL₃(2^m)′, graph PSL₂(2^n)′, graph-field
PSU₃(2^m), and exceptional E₉ residual rows. The unitary row specifies the
actual Hermitian matrix form, Frobenius, and fixed-field order. Neither model
nonsolvability nor numerical separation is assumed by this input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.2–4, printed pp.1170–1171; proof of 16.4.11(2), printed p.1193.
The parent source-theorem assembly must discharge the displayed table input.
-/

public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies

/-- The consumed outer rows, stated on the actual PSL₃ matrix carrier.
The alternatives are field,
graph, graph-field over a larger fixed field, and the exceptional E₉ row. -/
structure LinearThreeInvolutionRows (F : Type*) [Field F] (n : ℕ) : Prop where
  outer_residual : ∀ a : MulAut PSL(3,F), orderOf a = 2 →
    (¬ ∃ x, a = MulAut.conj x) →
    (∃ m : ℕ, 0 < m ∧ n = 2 * m ∧
      Nonempty (pResidual 2 a.fixedSubgroup ≃*
        commutator PSL(3, BinaryGaloisField m))) ∨
    Nonempty (pResidual 2 a.fixedSubgroup ≃*
      commutator (PSL2BinaryMatrixGroup n)) ∨
    (∃ m : ℕ, 2 ≤ m ∧ n = 2 * m ∧ ∃ J : HermitianForm 3 F,
      J.form = !![0,0,1; 0,1,0; 1,0,0] ∧
      (∀ x, J.conj x = x ^ (2 ^ m)) ∧
      Nat.card {x : F // J.conj x = x} = 2 ^ m ∧
      Nonempty (pResidual 2 a.fixedSubgroup ≃* ProjectiveSpecialUnitaryMatrixGroup J)) ∨
    (n = 2 ∧ Nonempty (pResidual 2 a.fixedSubgroup ≃*
      Multiplicative (Fin 2 → ZMod 3)))

/-- The earlier involution-table input, over every actual field witness.
No exclusion or numerical separation is assumed. -/
@[expose] def LinearThreeInvolutionTable : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 1 ≤ n →
    Nat.card F = 2 ^ n → LinearThreeInvolutionRows F n

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

private theorem false_of_small_inner (d : Contrary T z L g R r)
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : n = 1 ∨ n = 2)
    (c : (L ⧸ center L) ≃* PSL(3,F))
    (ei : (innerAction d c).fixedSubgroup ≃*
      Matrix.PSL3.EvenInnerCentralizers.centralizer F)
    (ho : 3 ∣ Nat.card (pResidual 2 (outerAction d c).fixedSubgroup)) : False := by
  have hout : 3 ∣ Nat.card (centralImage (L.conjBy g) (residual (L.conjBy g) z)) := by
    rwa [Nat.card_congr (outerResidualEquiv d c).toEquiv]
  have hin := OtherFamilies.outer_odd_prime_dvd_inner d Nat.prime_three (by decide) hout
  rw [Nat.card_congr (innerResidualEquiv d c).toEquiv] at hin
  have hfix := (OtherFamilies.odd_prime_dvd_residual_iff Nat.prime_three (by decide)).mp hin
  rw [Nat.card_congr ei.toEquiv] at hfix
  exact Matrix.PSL3Even.ResidualComparison.root_centralizer_small F hn hF hfix

/-- The PSL₃ comparison for one field, conditional only on the exact earlier
involution rows. All central covering kernels are retained. -/
theorem not_linear_three_model (d : Contrary T z L g R r)
    {F : Type*} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* PSL(3,F))
    (rows : LinearThreeInvolutionRows F n) : False := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let c := (LiePreliminaries.centerQuotientEquivTwoCore (component_oddCore d)).trans e
  obtain ⟨ei⟩ := Matrix.PSL3Even.ResidualComparison.inner_fixed_equiv_root F hn hF (innerAction d c)
    (innerAction_order d c) (innerAction_inner d c)
  have hi : Group.IsSolvable (innerAction d c).fixedSubgroup := by
    let := Matrix.PSL3Even.ResidualComparison.root_centralizer_solvable F hn hF
    exact Group.isSolvable_of_surjective (f := ei.symm.toMonoidHom) ei.symm.surjective
  rcases rows.outer_residual (outerAction d c)
      (outerAction_order d c) (outerAction_outer d c) with hf | hg | hgf | hsmall
  · obtain ⟨m, _, _, ⟨eo⟩⟩ := hf
    apply false_of_solvable_inner_nonsolvable_outer d c hi
    intro ho
    let := ho
    exact Matrix.PSL3Even.ResidualComparison.psl_three_commutator_not_solvable (BinaryGaloisField m)
      (Group.isSolvable_of_surjective (f := eo.toMonoidHom) eo.surjective)
  · obtain ⟨eo⟩ := hg
    by_cases hn2 : 2 ≤ n
    · apply false_of_solvable_inner_nonsolvable_outer d c hi
      intro ho
      let := ho
      exact Matrix.PSL3Even.ResidualComparison.binary_psl_two_commutator_not_solvable hn2
        (Group.isSolvable_of_surjective (f := eo.toMonoidHom) eo.surjective)
    · apply false_of_small_inner d hF (Or.inl (by omega)) c ei
      rw [Nat.card_congr eo.toEquiv]
      exact Matrix.PSL3Even.ResidualComparison.three_dvd_binary_psl_two_commutator hn
  · obtain ⟨m, hm, hnm, J, hJ, _, hfixed, ⟨eo⟩⟩ := hgf
    apply false_of_solvable_inner_nonsolvable_outer d c hi
    intro ho
    let := ho
    apply Matrix.PSL3Even.ResidualComparison.unitary_not_solvable J hm (by
      rw [hF, hnm, mul_comm 2 m, pow_mul]) hfixed hJ
    exact Group.isSolvable_of_surjective (f := eo.toMonoidHom) eo.surjective
  · obtain ⟨hn2, ⟨eo⟩⟩ := hsmall
    apply false_of_small_inner d hF (Or.inr hn2) c ei
    rw [Nat.card_congr eo.toEquiv]
    change 3 ∣ Nat.card (Fin 2 → ZMod 3)
    norm_num [Nat.card_fun]

/-- The PSL₃ family alternative in the reverse-Δ₀ comparison. The table
argument remains an explicit earlier-source obligation for final assembly. -/
theorem not_psl_three_quotient (d : Contrary T z L g R r)
    (rows : LinearThreeInvolutionTable) {n : ℕ} (hn : 1 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 (2 ^ n)) : False := by
  obtain ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ := hmodel
  exact not_linear_three_model d hn hF e (rows F n hn hF)

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
