module

public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.BinaryLieModels
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.SourceSetup
public import Theory.SpecificGroups.ClassicalMatrixLowRanks
public import Theory.SpecificGroups.ClassicalOrthogonal.SourcePredicateLowRanks
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.SourcePredicatePlane

/-!
# The unrestricted Chapter 13 Lie predicate and the Theorem D family input

Chapter 13 quantifies over every natural-number classical parameter. For a
nonabelian simple group the actual low-rank carriers force the guards used
by `IsBinaryLieModelAt`: the degenerate linear, unitary, symplectic, split and
odd carriers are trivial; the split rank-two carrier is a product of two
SL₂ groups; and both truncated minus ranks are quotients of the abelian
derived isometry group of an anisotropic plane. These facts concern the
literal elementary/scalar and derived/scalar constructions.

All surviving field, rank, and Hermitian-form witnesses are retained. The
exceptional and twisted constructors transport directly; the odd-exponent
Suzuki and Ree parameters satisfy their lower bound by arithmetic. Applying
this comparison to the guarded-family exclusion gives exactly the
`no_larger_field` clause of the existing Chapter 13 counterexample setup.

Source: Aschbacher–Smith Hypothesis 13.3.1(2), printed p.884, and the opening
reduction in Theorem 14.8.2 (Theorem D), printed pp.1078–1079. Classical
simple parameter ranges: GLS3 Theorem 2.2.7 and §2.7.
-/

@[expose] public section

open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ClassicalOrthogonal.SourcePredicateLowRanks

universe u
variable {G : Type u} [Group G]

private theorem charTwo_of_binary_card {F : Type} [Field F] [Finite F]
    {f : ℕ} (hcard : Nat.card F = 2 ^ f) : CharP F 2 := by
  let : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (by simpa only [← Nat.card_eq_fintype_card] using hcard)

private theorem linear_guard [Nontrivial G] {d q : ℕ}
    (h : ClassicalGroup.IsPSL G d q) : 2 ≤ d := by
  by_contra hd
  obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
  let := ClassicalMatrixLowRanks.psl_subsingleton F d (by omega)
  have : Subsingleton G := e.injective.subsingleton
  exact false_of_nontrivial_of_subsingleton G

private theorem unitary_guard [Nontrivial G] {d q : ℕ}
    (h : ClassicalGroup.IsPSU G d q) : 2 ≤ d := by
  by_contra hd
  obtain ⟨F, hF, hfin, J, _, _, ⟨e⟩⟩ := h
  let := ClassicalMatrixLowRanks.psu_subsingleton F d (by omega) J
  have : Subsingleton G := e.injective.subsingleton
  exact false_of_nontrivial_of_subsingleton G

private theorem symplectic_guard [Nontrivial G] {r q : ℕ}
    (h : ClassicalGroup.IsPSp G r q) : 1 ≤ r := by
  by_contra hr
  have hr0 : r = 0 := by omega
  subst r
  obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
  let := ClassicalMatrixLowRanks.psp_zero_subsingleton F
  have : Subsingleton G := e.injective.subsingleton
  exact false_of_nontrivial_of_subsingleton G

private theorem orthogonalPlus_guard [IsSimpleGroup G] {r f : ℕ}
    (h : ClassicalGroup.IsPOmegaPlus G r (2 ^ f)) : 3 ≤ r := by
  by_contra hr
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
  have hrsmall : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hrsmall with rfl | rfl | rfl
  · let := pOmegaPlus_zero_subsingleton F
    have : Subsingleton G := e.injective.subsingleton
    exact false_of_nontrivial_of_subsingleton G
  · let := pOmegaPlus_one_subsingleton F
    have : Subsingleton G := e.injective.subsingleton
    exact false_of_nontrivial_of_subsingleton G
  · let := charTwo_of_binary_card hcard
    exact not_isSimpleGroup_pOmegaPlus_two F e.symm.isSimpleGroup

private theorem orthogonalOdd_guard [Nontrivial G] {r q : ℕ}
    (h : ClassicalGroup.IsPOmegaOdd G r q) : 1 ≤ r := by
  by_contra hr
  have hr0 : r = 0 := by omega
  subst r
  obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
  let := pOmegaOdd_zero_subsingleton F
  have : Subsingleton G := e.injective.subsingleton
  exact false_of_nontrivial_of_subsingleton G

private theorem orthogonalMinus_guard (hnab : ¬ IsMulCommutative G) {r f : ℕ}
    (h : ClassicalGroup.IsPOmegaMinus G r (2 ^ f)) : 2 ≤ r := by
  by_contra hr
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
  let := charTwo_of_binary_card hcard
  let := ClassicalOrthogonal.Minus.SourcePredicatePlane.pOmegaMinus_commutative_of_le_one
    F r (by omega)
  apply hnab
  apply IsMulCommutative.of_comm
  intro x y
  apply e.injective
  simp only [map_mul, mul_comm]

/-- Nonabelian simplicity removes precisely the degenerate classical parameters
from the literal, unrestricted Chapter 13 predicate. No extra rank exclusions
or classification premise are required. -/
theorem isBinaryLieModelAt_of_largerEvenFieldModel [IsSimpleGroup G]
    (hnab : ¬ IsMulCommutative G) (hmodel : LargerEvenFieldModel G) :
    ∃ f : ℕ, 1 < f ∧ IsBinaryLieModelAt G f := by
  obtain ⟨f, hf, hm⟩ := hmodel
  refine ⟨f, hf, ?_⟩
  rcases hm with ⟨d, hm⟩ | hg2 | hf4 | he6 | he7 | he8 | htwisted | htriality | ⟨m, hm, hsuz | hree⟩
  · rcases hm with hlin | huni | hsymp | hplus | hodd | hminus
    · exact .linear d (linear_guard hlin) hlin
    · exact .unitary d (unitary_guard huni) huni
    · exact .symplectic d (symplectic_guard hsymp) hsymp
    · exact .orthogonalPlus d (orthogonalPlus_guard hplus) hplus
    · exact .orthogonalOdd d (orthogonalOdd_guard hodd) hodd
    · exact .orthogonalMinus d (orthogonalMinus_guard hnab hminus) hminus
  · exact .g2 hg2
  · exact .f4 hf4
  · exact .e6 he6
  · exact .e7 he7
  · exact .e8 he8
  · exact .twistedE6 htwisted
  · exact .triality htriality
  · exact .suzuki m (by omega) hm hsuz
  · exact .reeF4 m (by omega) hm hree

/-- The forward comparison under exactly the simple-QTKE hypothesis supplied
by the Theorem D consumer, with the full known-simple catalogue. -/
theorem isBinaryLieModelAt_of_largerEvenFieldModel_of_isSimpleQTKE [Finite G]
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hmodel : LargerEvenFieldModel G) :
    ∃ f : ℕ, 1 < f ∧ IsBinaryLieModelAt G f := by
  let := h.simple
  exact isBinaryLieModelAt_of_largerEvenFieldModel h.nonabelian hmodel

/-- The exact `Counterexample.no_larger_field` clause of Chapter 13 follows
from the complete guarded-family exclusion used in Theorem D. -/
theorem no_larger_field_of_guarded_exclusion [Finite G]
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hexclude : ∀ f : ℕ, 1 < f → ¬ IsBinaryLieModelAt G f) :
    ¬ LargerEvenFieldModel G := by
  intro hmodel
  obtain ⟨f, hf, hm⟩ := isBinaryLieModelAt_of_largerEvenFieldModel_of_isSimpleQTKE h hmodel
  exact hexclude f hf hm

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
