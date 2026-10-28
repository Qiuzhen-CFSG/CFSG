module
public import CFSG.Quasithin.ChapterD.Section03.EvenHermitianExclusion
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.EvenHermitianSchur

/-!
# Only the whole natural tensor remains on the nonseparated original seed

Four invariant copies of each factor's type cost four times its conjugation
image rank. A Hermitian type costs strictly more. The two images together
detect the full preserving actor, contradicting its two-rank displacement
budget. If both types are natural, the whole seed already has dimension 4n.
Thus the genuine two-kernel Hermitian case is excluded in either orientation.

This applies to the literal original Hall consumer, retaining the quotient's
exact O₂ kernel, both component restrictions and originalSeedAction. The output
is now a genuine whole-space natural tensor, not a disjunction containing an
unexcluded Hermitian alternative. Ambient exclusion of that tensor and final
SourceNonnormalCentralHallAt assembly remain with this owner.
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

/-- Whole-seed natural-tensor coordinates with the literal quotient and both factor markings. -/
def OriginalEvenNaturalTensorAnalysis {t : G} (ht : t ∈ (T : Subgroup G)) (n : ℕ)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)) : Prop :=
  ∃ q : localOrbit T L →* SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n),
    Function.Surjective q ∧ q.ker = pCore 2 (localOrbit T L) ∧
    (∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ = (e (QuotientGroup.mk' _ l),1)) ∧
    (∀ l : L, q (originalConjugateOrbitInclusion ht l) = (1,e (QuotientGroup.mk' _ l))) ∧
    ∃ σ : Representation (ZMod 2)
        (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) (Additive D.seed),
      σ.IsIrreducible ∧ Function.Injective σ ∧ σ.comp q = originalSeedAction D ∧
      (∃ α : MulAut SL(2,GaloisField 2 n), Nonempty (σ.Equiv (restrictScalars (k := ZMod 2)
        (externalTensor
          ((SL2.BinarySmall.embeddedNatural (RingHom.id (GaloisField 2 n))).comp α.symm.toMonoidHom)
          (SL2.BinarySmall.embeddedNatural (RingHom.id (GaloisField 2 n)))))))

/-- Exclude the genuine Hermitian case while retaining the original whole-seed marking. -/
theorem original_even_seed_natural_tensor
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) : OriginalEvenNaturalTensorAnalysis D ht n e := by
  let := D.quasisimple
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_simple D c.nonnormal
  let : IsSimpleGroup SL(2,GaloisField 2 n) := e.symm.isSimpleGroup
  let : IsQuasisimple SL(2,GaloisField 2 n) := IsQuasisimple.of_mulEquiv e
  let : FiniteDimensional (ZMod 2) (Additive D.seed) := Module.Finite.of_finite
  obtain ⟨q,hq,hker,hl,hr,σ,hi,hf,hσ,hm⟩ :=
    original_even_seed_natural_or_hermitian_schur_linear D c n hn e ht htn hsep
  refine ⟨q,hq,hker,hl,hr,σ,hi,hf,hσ,?_⟩
  exact hm.resolve_right (fun h => ChapterD.not_even_square_hermitian_multiplicity σ hi hf
    (IsSQTK.knownSimple_of_equiv e (original_component_quotient_sqtk D)) h.1)

/-- The exact whole-seed dimension in every remaining field degree. -/
theorem original_nonseparated_even_seed_finrank_eq
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    Module.finrank (ZMod 2) (Additive D.seed) = 4*n := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,⟨a⟩⟩ := original_even_seed_natural_tensor D c n hn e ht htn hsep
  exact a.toLinearEquiv.finrank_eq.trans
    (NaturalTensor.finrank_tensor (GaloisField 2 n) (GaloisField.card 2 n (by omega)))

/-- The original ambient residual now contains only an actual natural tensor. -/
def OriginalNonseparatedNaturalTensorCase : Prop :=
  ∃ (t : G) (ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
    ∃ n : ℕ, 3 ≤ n ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n),
      ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
        D.seed ≤ centralizer (L : Set G)) ∧ OriginalEvenNaturalTensorAnalysis D ht n e

/-- The original Hall conclusion or the sole remaining ambient natural tensor. -/
theorem original_hall_conclusion_or_natural_tensor
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    (IsPGroup 3 B ∨ ∃ n : ℕ, Monoid.exponent B ∣ 2^n+1) ∨
      OriginalNonseparatedNaturalTensorCase D := by
  rcases original_hall_conclusion_or_even_schur_linear_analysis D c with hh |
      ⟨t,ht,htn,n,hn,e,hsep,_⟩
  · exact Or.inl hh
  · exact Or.inr ⟨t,ht,htn,n,hn,e,hsep,
      original_even_seed_natural_tensor D c n hn e ht htn hsep⟩
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
