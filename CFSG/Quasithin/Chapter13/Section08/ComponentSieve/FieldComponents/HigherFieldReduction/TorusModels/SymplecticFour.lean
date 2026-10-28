module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.Alignment
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.Actions
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.IntrinsicActors

/-!
# The intrinsic Sp₄ Borel and its torus in the higher-field reduction

For the actual symplectic matrix group, the Borel attached to a specified
Sylow two-subgroup S is N(S). Its two-core is S. Its two-residual has core
S ∩ O²(N(S)) and quotient isomorphic to the full split torus Fˣ × Fˣ.
The imported matrix calculation intertwines field and exceptional graph
automorphisms with the concrete torus actions; the graph action squares to
Frobenius. The field-involution displacement has order (2^m+1)², exceeding
three also over F₄.

For every acting two-group stabilizing S and containing its inner image,
the fixer of O³(B)O₂(B)/O₂(B) is precisely that image unless n = 2 or 6.
In those degrees every outer actor has commutator quotient of order greater
than three; Sp₄(4) is not a small exception. The imported proofs account for
arbitrary two-power graph actors and discharge all torus arithmetic premises.

These are the intrinsic Sp₄ calculations used in Aschbacher–Smith 13.8.20,
printed p.954. Only the explicitly typed earlier classification of
diagram-preserving automorphisms remains an input. The parent source
assembly must retain C_T(K) on ambient lifting, as in the imported residual
module; this module works in the actual automorphism action image.
-/

public section

open Subgroup
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels

variable {F : Type*} [Field F] [Finite F]

/-- Both source Borel quotients, with their two-cores and the specified Sylow aligned. -/
theorem symplecticFour_borel_quotients {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 1 < n) (S : Sylow 2 (Sp F)) :
    let B₀ := normalizer (S : Set (Sp F))
    let B := borelResidual B₀
    B₀.pCoreIn 2 = (S : Subgroup (Sp F)) ∧
      B.pCoreIn 2 = (S : Subgroup (Sp F)) ⊓ B ∧
      Nonempty (B₀ ⧸ pCore 2 B₀ ≃* (Fˣ × Fˣ)) ∧
      Nonempty (B ⧸ pCore 2 B ≃* (Fˣ × Fˣ)) := by
  have hn' : 1 ≤ n := by omega
  exact ⟨EvenBorelTorus.borelAt_twoCoreIn hF hn' S,
    EvenBorelTorus.residualAt_twoCoreIn hF hn' S,
    ⟨EvenBorelTorus.borelAtQuotientEquiv hF hn' S⟩,
    ⟨EvenBorelTorus.residualAtQuotientEquiv hF hn' S⟩⟩

/-- Passing to the source two-residual keeps both split torus factors. -/
theorem symplecticFour_residual_torus_card {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 1 < n) (S : Sylow 2 (Sp F)) :
    let B := borelResidual (normalizer (S : Set (Sp F)))
    Nat.card (B ⧸ pCore 2 B) = (2 ^ n - 1) ^ 2 := by
  change Nat.card (EvenBorelTorus.residualAt S ⧸ pCore 2 (EvenBorelTorus.residualAt S)) = _
  rw [Nat.card_congr (EvenBorelTorus.residualAtQuotientEquiv hF (by omega) S).toEquiv,
    Nat.card_prod, Nat.card_units, hF, pow_two]

variable [CharP F 2]

/-- The intrinsic Sp₄ case of the source torus-centralizer alternative. -/
theorem symplecticFour_fixes_residual_iff_mem_innerSylow {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), DiagramAutomorphisms.PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F,
        a = MulAut.conj g * DiagramAutomorphisms.fieldAutomorphism σ)
    (hn2 : n ≠ 2) (hn6 : n ≠ 6)
    (S : Sylow 2 (Sp F)) (A : Subgroup (MulAut (Sp F))) (hA : IsPGroup 2 A)
    (hI : (S : Subgroup (Sp F)).map (MulAut.conj : Sp F →* MulAut (Sp F)) ≤ A)
    (hS : ∀ a ∈ A, (S : Subgroup (Sp F)).map a.toMonoidHom = S)
    {a : MulAut (Sp F)} (ha : a ∈ A) :
    let B := borelResidual (normalizer (S : Set (Sp F)))
    (∀ b ∈ residualIn 3 B ⊔ B.pCoreIn 2, b⁻¹ * a b ∈ B.pCoreIn 2) ↔
      a ∈ (S : Subgroup (Sp F)).map (MulAut.conj : Sp F →* MulAut (Sp F)) :=
  EvenBorelTorus.IntrinsicActors.fixes_residualAt_iff_mem_innerSylow
    hF hn hclass hn2 hn6 S A hA hI hS ha

/-- Neither Sp₄(4) nor Sp₄(64) permits the source's small outer commutator exception. -/
theorem symplecticFour_three_lt_commutator_quotient {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), DiagramAutomorphisms.PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F,
        a = MulAut.conj g * DiagramAutomorphisms.fieldAutomorphism σ)
    (hsmall : n = 2 ∨ n = 6)
    (S : Sylow 2 (Sp F)) (A : Subgroup (MulAut (Sp F))) (hA : IsPGroup 2 A)
    (hS : ∀ a ∈ A, (S : Subgroup (Sp F)).map a.toMonoidHom = S)
    {a : MulAut (Sp F)} (ha : a ∈ A) (houter : a ∉ MulAut.innerSubgroup (Sp F)) :
    let B := borelResidual (normalizer (S : Set (Sp F)))
    let C := commutatorSubgroup (zpowers a) (Sp F) B
    3 < Nat.card (C ⧸ pCore 2 C) :=
  EvenBorelTorus.IntrinsicActors.three_lt_commutator_quotient
    hF hn hclass hsmall S A hA hS ha houter

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels
