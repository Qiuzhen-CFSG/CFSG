module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Setup
public import Theory.GroupTheory.CComponent.Basic
public import Theory.GroupTheory.ConjugateSpanOrder
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.RegularWreathProduct

/-!
# The literal conclusions to be established in 14.6.14

These predicates specify the normal closure of O²(H) in the chosen Mc.
Component membership is relative to Mc, the product uses conjugation by
s⁻¹, and each model alternative is an isomorphism of the actual Mc/O₂(Mc).
The four alternatives are a target interface, not a classification theorem.
Their proof must retain `MaximalOddPrime` from the paragraph on p.1032.

Separating this interface lets the quintic exclusion and the normalizer
arguments proceed from an explicit 14.6.14 premise while its own producer
constructs that premise. No axiom or instance supplies the alternatives.

Source: Aschbacher--Smith 14.6.14, printed pp.1032--1033.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G]

/-- The subgroup K_z = ⟨O²(H)^Mc⟩ in the original ambient group. -/
noncomputable def residualClosure (H Mc : Subgroup G) : Subgroup G :=
  conjugateSpanBy (residual H) Mc

/-- The actual product of a source component and its exchanged conjugate.
Component subnormality is relative to Mc. The concrete quotient models
in `SourceClosureAlternatives` use the separate two-core quotient of Mc. -/
def ExchangedComponentClosure (T Mc Kz : Subgroup G) : Prop :=
  ∃ K1 : Subgroup G, K1 ≤ Mc ∧ (K1.subgroupOf Mc).IsCComponent ∧
    ∃ s ∈ T, s ∉ normalizer (K1 : Set G) ∧
      (Kz : Set G) = (K1 : Set G) *
        (K1.map (MulAut.conj s⁻¹).toMonoidHom : Set G)

/-- Exactly the four alternatives of original 14.6.14, including the
conditional {2,3}-order assertion and the full automorphism/wreath models. -/
def SourceClosureAlternatives (T Mc H : Subgroup G) (p : ℕ) : Prop :=
  let Kz := residualClosure H Mc
  (Kz = residual H ∧
    (p = 3 → ∀ q : ℕ, q.Prime → q ∣ Nat.card Mc → q = 2 ∨ q = 3)) ∨
  (p = 3 ∧ Kz ≤ Mc ∧ (Kz.subgroupOf Mc).IsCComponent ∧
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ Nonempty ((Mc ⧸ pCore 2 Mc) ≃*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)))) ∨
  (p = 3 ∧ ExchangedComponentClosure T Mc Kz ∧
    (Nonempty ((Mc ⧸ pCore 2 Mc) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))) ∨
     Nonempty ((Mc ⧸ pCore 2 Mc) ≃*
      RegularWreathProduct (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
        (Multiplicative (ZMod 2))))) ∨
  (p = 5 ∧ ExchangedComponentClosure T Mc Kz ∧
    Nonempty ((Mc ⧸ pCore 2 Mc) ≃*
      RegularWreathProduct
        (MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)))
        (Multiplicative (ZMod 2))))

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
