module
public import CFSG.Quasithin.ChapterD.Section03.EvenHermitianMultiplicity
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.EvenHermitianKernel

/-!
# Hermitian multiplicity on the literal original seed

The remaining nonseparated seed is a natural tensor of dimension 4n, or has
dimension at least 8n and a genuine faithful multiplicity action over its
Hermitian fixed half-field. The latter action is constructed on the whole seed,
with both component intertwiners. Both nonzero actor kernels are retained.
The full preserving actor has rank at most 2n; any member moving the Schur
field forces dimension 8n, actor rank 2n and fixed codimension 4n.

The exact original orbit quotient, its two-core kernel, its two restrictions,
and the equality with the original seed action are unchanged. The literal Hall
consumer gains this stronger alternative without any new premise. The Hermitian
and ambient natural-tensor exclusions still belong to the source assembly.
Source: Aschbacher--Smith D.3.7 and10.1.1--2,10.2.3, printed pp.198--199,
741--742,745; refs/quasithin.pdf.
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
def OriginalEvenHermitianMultiplicityAnalysis {t : G} (ht : t ∈ (T : Subgroup G)) (n : ℕ)
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
        ChapterD.EvenSquareHermitianMultiplicity σ)

/-- Construct the actual half-field multiplicity action from the original
Hall context, including either orientation of the Hermitian constituent. -/
theorem original_even_seed_natural_or_hermitian_multiplicity
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) : OriginalEvenHermitianMultiplicityAnalysis D ht n e := by
  let := D.quasisimple
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_simple D c.nonnormal
  let : IsSimpleGroup SL(2,GaloisField 2 n) := e.symm.isSimpleGroup
  let : IsQuasisimple SL(2,GaloisField 2 n) := IsQuasisimple.of_mulEquiv e
  let : FiniteDimensional (ZMod 2) (Additive D.seed) := Module.Finite.of_finite
  obtain ⟨q,hq,hker,hl,hr,σ,hi,hf,hσ,hm⟩ :=
    original_even_seed_natural_or_hermitian_kernel D c n hn e ht htn hsep
  refine ⟨q,hq,hker,hl,hr,σ,hi,hf,hσ,?_⟩
  exact hm.imp id (ChapterD.even_square_hermitian_multiplicity σ hi hf)

/-- There is a genuine gap between the natural tensor and every remaining
Hermitian seed, measured on the unchanged original binary carrier. -/
theorem original_even_seed_dimension_gap
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    Module.finrank (ZMod 2) (Additive D.seed) = 4*n ∨
      8*n ≤ Module.finrank (ZMod 2) (Additive D.seed) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hm⟩ :=
    original_even_seed_natural_or_hermitian_multiplicity D c n hn e ht htn hsep
  rcases hm with ⟨_,⟨a⟩⟩ | hm
  · exact Or.inl (a.toLinearEquiv.finrank_eq.trans
      (NaturalTensor.finrank_tensor (GaloisField 2 n) (GaloisField.card 2 n (by omega))))
  · exact Or.inr hm.2.1

/-- Both remaining alternatives are retained, with actual multiplicity
coordinates and the lower bound in the Hermitian branch. -/
def OriginalNonseparatedEvenMultiplicityCase : Prop :=
  ∃ (t : G) (ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
    ∃ n : ℕ, 3 ≤ n ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n),
      ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
        D.seed ≤ centralizer (L : Set G)) ∧ OriginalEvenHermitianMultiplicityAnalysis D ht n e

/-- Apply the constructed faithful multiplicity action to the literal Hall
consumer, with all original hypotheses and no extra recognition callback. -/
theorem original_hall_conclusion_or_even_multiplicity_analysis
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    (IsPGroup 3 B ∨ ∃ n : ℕ, Monoid.exponent B ∣ 2^n+1) ∨
      OriginalNonseparatedEvenMultiplicityCase D := by
  rcases original_hall_conclusion_or_even_hermitian_analysis D c with hh |
      ⟨t,ht,htn,n,hn,e,hsep,_⟩
  · exact Or.inl hh
  · exact Or.inr ⟨t,ht,htn,n,hn,e,hsep,
      original_even_seed_natural_or_hermitian_multiplicity D c n hn e ht htn hsep⟩
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
