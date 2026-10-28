module
public import CFSG.Quasithin.ChapterD.Section03.EvenHermitianSchur
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.EvenHermitianMultiplicity

/-!
# Schur-linear residual actors on the literal original seed

The remaining alternative retains the whole natural tensor, or the actual
Hermitian multiplicity action with both component kernels. Every preserving
starred actor in the latter case is now linear over the original Schur field.
The strict half-space bound excludes Schur-moving actors from the full rank
budget, without replacing the full actor by a faithful one-factor image.

The literal quotient map still has kernel O₂(localOrbit), the same two component
restrictions, and composition equal to originalSeedAction. This strengthens the
actual Hall consumer without a new premise. The Schur-linear Hermitian case and
ambient natural-tensor exclusion remain with this source owner.
Source: Aschbacher--Smith D.3.7 and10.1.1--2,10.2.3, pp.198--199,741--742,745.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.QuadraticFourGroup.TensorClassification
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary
local instance (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2

/-- The multiplicity action retains the literal quotient and both component
markings; in the Hermitian branch it is attached to the same full seed. -/
def OriginalEvenHermitianLinearAnalysis {t : G} (ht : t ∈ (T : Subgroup G)) (n : ℕ)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)) : Prop :=
  ∃ q : localOrbit T L →* SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n),
    Function.Surjective q ∧ q.ker = pCore 2 (localOrbit T L) ∧
    (∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ = (e (QuotientGroup.mk' _ l),1)) ∧
    (∀ l : L, q (originalConjugateOrbitInclusion ht l) = (1,e (QuotientGroup.mk' _ l))) ∧
    ∃ σ : Representation (ZMod 2)
        (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) (Additive D.seed),
      σ.IsIrreducible ∧ Function.Injective σ ∧ σ.comp q = originalSeedAction D ∧
      ((∃ α : MulAut SL(2,GaloisField 2 n), Nonempty (σ.Equiv (restrictScalars (k := ZMod 2)
        (externalTensor
          ((SL2.BinarySmall.embeddedNatural (RingHom.id (GaloisField 2 n))).comp α.symm.toMonoidHom)
          (SL2.BinarySmall.embeddedNatural (RingHom.id (GaloisField 2 n))))))) ∨
        ChapterD.EvenSquareHermitianLinearMultiplicity σ)

/-- Remove every Schur-moving preserving actor in the actual Hall context. -/
theorem original_even_seed_natural_or_hermitian_schur_linear
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) : OriginalEvenHermitianLinearAnalysis D ht n e := by
  let : FiniteDimensional (ZMod 2) (Additive D.seed) := Module.Finite.of_finite
  obtain ⟨q,hq,hker,hl,hr,σ,hi,hf,hσ,hm⟩ :=
    original_even_seed_natural_or_hermitian_multiplicity D c n hn e ht htn hsep
  refine ⟨q,hq,hker,hl,hr,σ,hi,hf,hσ,?_⟩
  exact hm.imp id (ChapterD.even_square_hermitian_linear_multiplicity σ hi hf)

/-- Both original alternatives, with all remaining Hermitian actors Schur linear. -/
def OriginalNonseparatedEvenSchurLinearCase : Prop :=
  ∃ (t : G) (ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
    ∃ n : ℕ, 3 ≤ n ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n),
      ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
        D.seed ≤ centralizer (L : Set G)) ∧ OriginalEvenHermitianLinearAnalysis D ht n e

/-- Apply the strict Schur displacement argument to the literal Hall consumer. -/
theorem original_hall_conclusion_or_even_schur_linear_analysis
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    (IsPGroup 3 B ∨ ∃ n : ℕ, Monoid.exponent B ∣ 2^n+1) ∨
      OriginalNonseparatedEvenSchurLinearCase D := by
  rcases original_hall_conclusion_or_even_multiplicity_analysis D c with hh |
      ⟨t,ht,htn,n,hn,e,hsep,_⟩
  · exact Or.inl hh
  · exact Or.inr ⟨t,ht,htn,n,hn,e,hsep,
      original_even_seed_natural_or_hermitian_schur_linear D c n hn e ht htn hsep⟩
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
