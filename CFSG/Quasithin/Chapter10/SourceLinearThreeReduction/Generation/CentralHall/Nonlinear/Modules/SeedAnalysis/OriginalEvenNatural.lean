module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.OriginalEvenExchange
public import CFSG.Quasithin.ChapterD.Section03.EvenNaturalTensor

/-!
# The original seed has a constituent or a natural tensor

The bounded Schur-nonlinear exchange is now recognized as a whole-space
natural tensor, so no unresolved Schur-field alternative remains. Apply this
to the unchanged seed through its exact orbit projection, two-core kernel,
and both original component restrictions. The resulting dichotomy is applied
to the literal Hall subgroup in the final theorem.

Ambient exclusion of these remaining natural tensors, constituent minimality,
and SeedAnalysisAt/SourceNonnormalCentralHallAt assembly remain with
qt-d-10-nona5-central-hall-orders. The Hall theorem retains moved minimality
explicitly; recognizing the tensor does not exclude it.
Source: Aschbacher--Smith D.3.7, 3.2.6 and10.1.1--2,
printed pp.197--199,581,741--742.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance originalEvenNaturalElementary : IsElementaryAbelian 2 D.seed :=
  D.seed_elementary
local instance originalEvenNaturalGaloisAlgebra (n : ℕ) :
    Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2

/-- The constituent or natural-tensor conclusion on the original seed, with the
surjective orbit quotient and its two component restrictions recorded exactly. -/
def OriginalEvenNaturalAnalysis {t : G} (ht : t ∈ (T : Subgroup G)) (n : ℕ)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)) : Prop :=
    ∃ q : localOrbit T L →* SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n),
      Function.Surjective q ∧ q.ker = pCore 2 (localOrbit T L) ∧
      (∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ = (e (QuotientGroup.mk' _ l),1)) ∧
      (∀ l : L, q (originalConjugateOrbitInclusion ht l) = (1,e (QuotientGroup.mk' _ l))) ∧
      ∃ σ : Representation (ZMod 2)
          (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) (Additive D.seed),
        σ.IsIrreducible ∧ Function.Injective σ ∧ σ.comp q = originalSeedAction D ∧
        ChapterD.EvenSquareConstituentOrNatural σ n

/-- On the unchanged nonseparated seed every exchange is a whole-space
natural tensor, including exchanges that move the original Schur field.
The other branch retains an actual constituent of either original factor. -/
theorem original_even_seed_constituent_or_natural
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) : OriginalEvenNaturalAnalysis D ht n e := by
  let : FiniteDimensional (ZMod 2) (Additive D.seed) := Module.Finite.of_finite
  obtain ⟨q,hq,hker,hl,hr,σ,hi,hf,hσ,ha⟩ :=
    original_even_seed_tensor_analysis D c n hn e ht htn hsep
  exact ⟨q,hq,hker,hl,hr,σ,hi,hf,hσ,ChapterD.even_square_constituent_or_natural_tensor
    σ hi hf n hn (GaloisField.card 2 n (by omega)) ha⟩

/-- The source catalogue supplies the degree and exact component marking;
no even-linear or exchange model is imposed as an extra source hypothesis. -/
theorem original_nonseparated_even_constituent_or_natural
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    ∃ (n : ℕ), 3 ≤ n ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n),
      OriginalEvenNaturalAnalysis D ht n e := by
  obtain ⟨n,hn,⟨e⟩⟩ := original_nonseparated_even_marking D c hnot ht htn hsep
  exact ⟨n,hn,e,original_even_seed_constituent_or_natural D c n hn e ht htn hsep⟩

/-- The literal Hall consumer has the required exponent or an actual constituent or
a whole-space natural tensor on the original even-linear seed. Moved minimality, and exclusion of
the remaining alternatives, stay with this task's source assembly. -/
theorem hall_exponent_or_original_even_constituent_or_natural
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    (hmin : MovedMinimal D) :
    (∃ n : ℕ, 1<n ∧ Monoid.exponent B ∣ 2^n+1) ∨
    ∃ (t : G) (ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
      ∃ (n : ℕ), 3 ≤ n ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n),
        OriginalEvenNaturalAnalysis D ht n e := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  by_cases hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)
  · exact Or.inl (hall_exponent_of_moved_minimal_and_crossed T D c hnot ht htn hmin
      (full_moved_centralizes_opposite_of_seed_separated D ht htn hsep))
  · exact Or.inr ⟨t,ht,htn,original_nonseparated_even_constituent_or_natural D c hnot ht htn hsep⟩
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
