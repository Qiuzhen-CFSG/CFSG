module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Targets
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Statements
public import Theory.GroupTheory.GeneralizedFitting.Defs

/-!
# Intermediate model comparison in the strict closure argument

These are proof obligations for the two alternatives (i)--(ii) in the middle
of the proof of 14.6.14. In the exchanged case the field parameter remains
unrestricted apart from the source parity and congruence. In the invariant
case the automorphism model describes K₁T/O₂(K₁T), not Mc/O₂(Mc).

Consequently these predicates do not contain the final closure alternatives.
The subsequent residual/layer argument must identify the actual quotient's
generalized Fitting subgroup. Borel arithmetic and the original outside
subgroup argument must then determine the field and the whole outer action.
All component membership is relative to Mc; the conjugate uses s⁻¹.

Source: Aschbacher--Smith, proof of 14.6.14, printed p.1033.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G]

/-- The actual exchanged pair before the Borel field-parameter argument.
The models concern the literal component image in Mc/O₂(Mc). -/
def StrictExchangedModel (T Mc Kz L : Subgroup G) (p : ℕ) : Prop :=
  (∃ s ∈ T, s ∉ normalizer (L : Set G) ∧
    (Kz : Set G) = (L : Set G) *
      (L.map (MulAut.conj s⁻¹).toMonoidHom : Set G)) ∧
  ((∃ m : ℕ, 2 ≤ m ∧ Even m ∧ Nat.ModEq p (2 ^ m) 1 ∧
      ClassicalGroup.IsPSL
        ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 2 (2 ^ m)) ∨
    (p = 3 ∧ ClassicalGroup.IsPSL
      ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 3 2))

/-- The invariant component's Sylow join, before identifying the full Mc
quotient with it. The degree is literally four or five. -/
def StrictInvariantModel (T Kz L : Subgroup G) (p : ℕ) : Prop :=
  p = 3 ∧ Kz = L ∧ T ≤ normalizer (L : Set G) ∧
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
      Nonempty (((L ⊔ T : Subgroup G) ⧸ pCore 2 (L ⊔ T : Subgroup G)) ≃*
        MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)))

/-- The intermediate comparison of 1.3.4 with the applicable F.9.18 list.
No theorem in this module asserts this classification. -/
def StrictClosureComparison (T Mc Kz : Subgroup G) (p : ℕ) : Prop :=
  ∃ L : Subgroup G, L ≤ Mc ∧ (L.subgroupOf Mc).IsCComponent ∧
    IsQuasisimple (XiQuotient L) ∧ Kz = componentOrbit L T ∧
    (StrictExchangedModel T Mc Kz L p ∨ StrictInvariantModel T Kz L p)

/-- The intermediate Fitting identification on printed p.1033. This does
not identify the full quotient's automorphism group or outer action. -/
structure StrictClosureLayer (Mc Kz : Subgroup G) : Prop where
  fitting_eq_bot : fittingSubgroup (Mc ⧸ pCore 2 Mc) = ⊥
  image_eq_generalizedFitting :
    ((Kz.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) =
      generalizedFitting (Mc ⧸ pCore 2 Mc)

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
