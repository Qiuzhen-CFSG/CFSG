module
public import CFSG.Quasithin.ChapterD.Section03.EvenFaithfulPair
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.SuzukiMultiplicityExclusion

/-!
# The original nonseparated seed: natural tensor or two actor kernels

Apply the faithful-factor and exchanging-actor calculations to the unchanged
seed. A natural tensor is identified on the whole seed, including its component
twist. Every other configuration has one preserving starred actor with nonzero,
disjoint kernels on the two actual component images. The original orbit quotient,
its exact two-core kernel, both component restrictions, and the original Hall B
are retained. In particular the new kernel alternative has no faithful-actor or
constituent assumption for the source assembly to discharge.

This strengthens the remaining even-linear alternative; it does not exclude
these configurations. The two-kernel calculation and the ambient natural-tensor
exclusion remain with the central Hall source owner.
Source: Aschbacher--Smith D.3.7, D.3.9 and10.1.1--2,10.2.3,
printed pp.197--201,741--742,745; refs/quasithin.pdf.
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
local instance evenDoubleKernelElementary : IsElementaryAbelian 2 D.seed := D.seed_elementary
local instance evenDoubleKernelAlgebra (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) :=
  ZMod.algebra _ 2

/-- The refined original seed alternative retains all literal component maps. -/
def OriginalEvenKernelAnalysis {t : G} (ht : t ∈ (T : Subgroup G)) (n : ℕ)
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
        ChapterD.EvenSquareDoubleKernel σ)

/-- The exact original square has whole-space natural coordinates or one
starred actor with nontrivial disjoint kernels on both original factors. -/
theorem original_even_seed_natural_or_double_kernel
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) : OriginalEvenKernelAnalysis D ht n e := by
  let := D.quasisimple
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_simple D c.nonnormal
  let : IsSimpleGroup SL(2,GaloisField 2 n) := e.symm.isSimpleGroup
  let : IsQuasisimple SL(2,GaloisField 2 n) := IsQuasisimple.of_mulEquiv e
  let : FiniteDimensional (ZMod 2) (Additive D.seed) := Module.Finite.of_finite
  obtain ⟨q,hq,hker,hl,hr,σ,hi,hσ⟩ := original_seed_product_action D c e ht htn
  have hf := original_seed_product_faithful_of_not_separated D e ht hsep q hl hr σ hσ
  have himage : actionImage (originalSeedAction D) = actionImage σ := by
    rw [←hσ]
    ext x
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨q l,Units.ext rfl⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨l,rfl⟩ := hq g
      exact ⟨l,Units.ext rfl⟩
  have hsmall := original_seed_normalizer_cubic_of_not_separated D c ht htn hsep
  have hsmallσ : cubicRatio (normalizerRepresentation σ) ≤ 2 := by
    unfold normalizerRepresentation linearNormalizer at hsmall ⊢
    rwa [himage] at hsmall
  exact ⟨q,hq,hker,hl,hr,σ,hi,hf,hσ,ChapterD.even_square_natural_or_double_kernel
    σ hi hf (IsSQTK.knownSimple_of_equiv e (original_component_quotient_sqtk D))
    n hn (GaloisField.card 2 n (by omega)) hsmallσ⟩

/-- The sole remaining original seed case, strengthened by the two-kernel analysis. -/
def OriginalNonseparatedEvenKernelCase : Prop :=
  ∃ (t : G) (ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
    ∃ n : ℕ, 3 ≤ n ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n),
      ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
        D.seed ≤ centralizer (L : Set G)) ∧ OriginalEvenKernelAnalysis D ht n e

/-- The literal Hall consumer, after eliminating every faithful-factor
non-natural configuration and every non-natural exchanging configuration. -/
theorem original_hall_conclusion_or_even_kernel_analysis
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    (IsPGroup 3 B ∨ ∃ n : ℕ, Monoid.exponent B ∣ 2^n+1) ∨
      OriginalNonseparatedEvenKernelCase D := by
  rcases original_hall_conclusion_or_nonseparated_even D c with hh |
      ⟨t,ht,htn,n,hn,e,hsep,_⟩
  · exact Or.inl hh
  · exact Or.inr ⟨t,ht,htn,n,hn,e,hsep,
      original_even_seed_natural_or_double_kernel D c n hn e ht htn hsep⟩
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
