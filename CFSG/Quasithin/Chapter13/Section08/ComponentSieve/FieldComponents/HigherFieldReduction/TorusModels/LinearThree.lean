module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree.Borels
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree.Fixers
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree.SixCommutators
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree.Lifting
public import Theory.SpecificGroups.PSL3.CartanActions.ActorCoverage

/-!
# Intrinsic SL₃ and PSL₃ torus calculations for 13.8.20

For either actual carrier over a field of order 2ⁿ, n>1, the two-residual
of the normalizer of a specified Sylow two-subgroup equals that normalizer.
Its two-core is precisely the specified Sylow. The imported matrix
calculations construct the quotient equivalences with two unit parameters,
retaining the cubic scalar quotient for PSL₃.

Outside degrees two and six the actors fixing O³(B)O₂(B)/O₂(B) are exactly
the inner image of S. In degree six every outer actor has a cyclic Borel
commutator whose quotient by its two-core has order greater than three.
Consequently an outer fixer with commutator quotient of order at most three
forces degree two, the permitted (S)L₃(4) exception.

Both carriers use the same explicitly typed earlier classification input:
the projective standard automorphism subgroup is the full automorphism group.
The matrix calculations prove the Borel and quotient actions; perfectness
lifts the projective factorization to SL₃. No torus-action formula or
involution restriction is an input. These are calculations in the actual
automorphism image. The imported lifting theorems give the full ambient
preimage as the embedded Sylow joined with C_T(K), retaining the kernel.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954 (PDF p.971);
GLS3 Theorem 2.5.12 and §2.7 for the explicit earlier classification input.
-/

public section

open Subgroup
open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions.BorelQuotient
open Matrix.PSL3.CartanActions.ActorCoverage
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree
variable {F : Type*} [Field F] [Finite F]

/-- The two-core of the intrinsic special linear Borel is the specified Sylow. -/
theorem special_normalizer_twoCore {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 1 < n) (S : Sylow 2 SL(3,F)) :
    (normalizer (S : Set SL(3,F))).pCoreIn 2 = S := by
  rw [← special_residual_eq hF hn S]
  exact special_residual_twoCore hF hn S

/-- The two-core of the intrinsic projective Borel is the specified Sylow. -/
theorem projective_normalizer_twoCore {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 1 < n) (S : Sylow 2 PSL(3,F)) :
    (normalizer (S : Set PSL(3,F))).pCoreIn 2 = S := by
  rw [← projective_residual_eq hF hn S]
  exact projective_residual_twoCore hF hn S

/-- The actual special linear residual quotient has two independent unit parameters. -/
noncomputable def special_residual_quotientEquiv {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (S : Sylow 2 SL(3,F)) :
    intrinsicResidual S ⧸ pCore 2 (intrinsicResidual S) ≃* (Fˣ × Fˣ) := by
  rw [special_residual_eq hF hn S]
  exact sylowSLNormalizerQuotientEquiv F (by omega) hF S

/-- Projectivization retains precisely the diagonal cubic scalar kernel. -/
noncomputable def projective_residual_quotientEquiv {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (S : Sylow 2 PSL(3,F)) :
    intrinsicResidual S ⧸ pCore 2 (intrinsicResidual S) ≃*
      ((Fˣ × Fˣ) ⧸ cubicScalars F) := by
  rw [projective_residual_eq hF hn S]
  exact sylowNormalizerQuotientEquiv F (by omega) hF S

variable [CharP F 2]

/-- Degree-six SL₃ needs only the same projective classification input as the fixer theorem. -/
theorem special_six_outer_commutator_of_standard (hF : Nat.card F = 2 ^ 6)
    (hcover : standard F = ⊤) (S : Sylow 2 SL(3,F))
    (A : Subgroup (MulAut SL(3,F))) (hA : IsPGroup 2 A)
    (hstable : StabilizesSylow A S) (hinner : innerSylow S ≤ A)
    (α : MulAut SL(3,F)) (hα : α ∈ A) (ho : α ∉ MulAut.innerSubgroup SL(3,F)) :
    let C := commutatorSubgroup (zpowers α) SL(3,F) (intrinsicResidual S)
    3 < Nat.card (C ⧸ pCore 2 C) :=
  special_six_outer_commutator hF (specialCoverage_of_standard_eq_top F hcover)
    S A hA hstable hinner α hα ho

/-- Degree-six PSL₃ with the common earlier classification input. -/
theorem projective_six_outer_commutator_of_standard (hF : Nat.card F = 2 ^ 6)
    (hcover : standard F = ⊤) (S : Sylow 2 PSL(3,F))
    (A : Subgroup (MulAut PSL(3,F))) (hA : IsPGroup 2 A)
    (hstable : StabilizesSylow A S) (hinner : innerSylow S ≤ A)
    (α : MulAut PSL(3,F)) (hα : α ∈ A) (ho : α ∉ MulAut.innerSubgroup PSL(3,F)) :
    let C := commutatorSubgroup (zpowers α) PSL(3,F) (intrinsicResidual S)
    3 < Nat.card (C ⧸ pCore 2 C) :=
  projective_six_outer_commutator hF (projectiveCoverage_of_standard_eq_top F hcover)
    S A hA hstable hinner α hα ho

/-- The complete intrinsic SL₃ alternative consumed by source 13.8.20. -/
theorem special_actor_alternative {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hcover : standard F = ⊤) (S : Sylow 2 SL(3,F))
    (A : Subgroup (MulAut SL(3,F))) (hA : IsPGroup 2 A)
    (hstable : StabilizesSylow A S) (hinner : innerSylow S ≤ A) :
    (∀ α ∈ A, FixesResidualTorus (intrinsicResidual S) α ↔ α ∈ innerSylow S) ∨
    n = 2 ∨ (n = 6 ∧ ∀ α ∈ A, α ∉ MulAut.innerSubgroup SL(3,F) →
      let C := commutatorSubgroup (zpowers α) SL(3,F) (intrinsicResidual S)
      3 < Nat.card (C ⧸ pCore 2 C)) := by
  by_cases hn2 : n = 2
  · exact Or.inr (Or.inl hn2)
  by_cases hn6 : n = 6
  · subst n
    exact Or.inr (Or.inr ⟨rfl,
      special_six_outer_commutator_of_standard hF hcover S A hA hstable hinner⟩)
  · exact Or.inl (fun _ hα =>
      special_fixesResidualTorus_iff hF hn hn2 hn6 hcover S A hA hstable hinner hα)

/-- The complete intrinsic PSL₃ alternative, on the actual central quotient. -/
theorem projective_actor_alternative {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hcover : standard F = ⊤) (S : Sylow 2 PSL(3,F))
    (A : Subgroup (MulAut PSL(3,F))) (hA : IsPGroup 2 A)
    (hstable : StabilizesSylow A S) (hinner : innerSylow S ≤ A) :
    (∀ α ∈ A, FixesResidualTorus (intrinsicResidual S) α ↔ α ∈ innerSylow S) ∨
    n = 2 ∨ (n = 6 ∧ ∀ α ∈ A, α ∉ MulAut.innerSubgroup PSL(3,F) →
      let C := commutatorSubgroup (zpowers α) PSL(3,F) (intrinsicResidual S)
      3 < Nat.card (C ⧸ pCore 2 C)) := by
  by_cases hn2 : n = 2
  · exact Or.inr (Or.inl hn2)
  by_cases hn6 : n = 6
  · subst n
    exact Or.inr (Or.inr ⟨rfl,
      projective_six_outer_commutator_of_standard hF hcover S A hA hstable hinner⟩)
  · exact Or.inl (fun _ hα =>
      projective_fixesResidualTorus_iff hF hn hn2 hn6 hcover S A hA hstable hinner hα)

/-- The small-commutator outer-fixer case leaves precisely the allowed SL₃(4) degree. -/
theorem special_outer_fixer_small_commutator_degree_two {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hcover : standard F = ⊤)
    (S : Sylow 2 SL(3,F)) (A : Subgroup (MulAut SL(3,F))) (hA : IsPGroup 2 A)
    (hstable : StabilizesSylow A S) (hinner : innerSylow S ≤ A)
    (α : MulAut SL(3,F)) (hα : α ∈ A) (ho : α ∉ MulAut.innerSubgroup SL(3,F))
    (hfix : FixesResidualTorus (intrinsicResidual S) α)
    (hsmall : let C := commutatorSubgroup (zpowers α) SL(3,F) (intrinsicResidual S)
      Nat.card (C ⧸ pCore 2 C) ≤ 3) : n = 2 := by
  rcases special_actor_alternative hF hn hcover S A hA hstable hinner with h | h | ⟨_,h⟩
  · obtain ⟨s,_,hs⟩ := (h α hα).mp hfix
    exact (ho ⟨s,hs⟩).elim
  · exact h
  · exact (Nat.not_lt_of_ge hsmall (h α hα ho)).elim

/-- The same outer-fixer exclusion retains PSL₃(4), rather than the special linear cover. -/
theorem projective_outer_fixer_small_commutator_degree_two {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hcover : standard F = ⊤)
    (S : Sylow 2 PSL(3,F)) (A : Subgroup (MulAut PSL(3,F))) (hA : IsPGroup 2 A)
    (hstable : StabilizesSylow A S) (hinner : innerSylow S ≤ A)
    (α : MulAut PSL(3,F)) (hα : α ∈ A) (ho : α ∉ MulAut.innerSubgroup PSL(3,F))
    (hfix : FixesResidualTorus (intrinsicResidual S) α)
    (hsmall : let C := commutatorSubgroup (zpowers α) PSL(3,F) (intrinsicResidual S)
      Nat.card (C ⧸ pCore 2 C) ≤ 3) : n = 2 := by
  rcases projective_actor_alternative hF hn hcover S A hA hstable hinner with h | h | ⟨_,h⟩
  · obtain ⟨s,_,hs⟩ := (h α hα).mp hfix
    exact (ho ⟨s,hs⟩).elim
  · exact h
  · exact (Nat.not_lt_of_ge hsmall (h α hα ho)).elim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree
