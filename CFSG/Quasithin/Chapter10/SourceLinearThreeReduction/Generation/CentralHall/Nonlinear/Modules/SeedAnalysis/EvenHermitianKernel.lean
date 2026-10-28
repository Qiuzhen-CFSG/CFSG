module
public import CFSG.Quasithin.ChapterD.Section03.EvenKernelConstituents
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.EvenDoubleKernel

/-!
# The original even-linear seed: natural tensor or Hermitian kernels

Apply the two-kernel constituent calculation to the original Hall context.
Natural constituents on both factors identify the entire unchanged seed,
without discarding either actor kernel. Every remaining non-natural seed has
an actual Hermitian constituent over the fixed half-field, so its field degree
is even. In odd degree the seed has binary dimension exactly 4n.

The original orbit quotient, its exact two-core kernel, and both component
restrictions are retained, as is the literal Hall subgroup in the consumer.
No faithfulness, constituent or parity hypothesis is added to that consumer.
The Hermitian-kernel exclusion and the ambient natural-tensor exclusion still
belong to this source assembly; this module does not prove the unconditional
SourceNonnormalCentralHallAt contract.
Source: Aschbacher--Smith D.3.7 and10.1.1--2,10.2.3,
printed pp.198--199,741--742,745; refs/quasithin.pdf.
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

/-- The remaining seed alternatives retain the original orbit projection and
both exact component restrictions. The Hermitian branch retains both actor kernels. -/
def OriginalEvenHermitianAnalysis {t : G} (ht : t ∈ (T : Subgroup G)) (n : ℕ)
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
        ChapterD.EvenSquareHermitianKernel σ n)

/-- Natural constituents on both factors give the whole natural tensor, even
when neither factor detects the full starred actor. -/
theorem original_even_seed_natural_or_hermitian_kernel
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) : OriginalEvenHermitianAnalysis D ht n e := by
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
  exact ⟨q,hq,hker,hl,hr,σ,hi,hf,hσ,ChapterD.even_square_natural_or_hermitian_kernel
    σ hi hf (IsSQTK.knownSimple_of_equiv e (original_component_quotient_sqtk D)) hn hsmallσ⟩

/-- In odd field degree the unchanged seed is already of natural-tensor
size, including the case of nontrivial kernels on both original factors. -/
theorem original_even_seed_finrank_eq_of_odd_degree
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    Module.finrank (ZMod 2) (Additive D.seed) = 4*n := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hm⟩ :=
    original_even_seed_natural_or_hermitian_kernel D c n hn e ht htn hsep
  rcases hm with ⟨_,⟨a⟩⟩ | ⟨_,_,_,s,hs,_⟩
  · exact a.toLinearEquiv.finrank_eq.trans
      (NaturalTensor.finrank_tensor (GaloisField 2 n) (GaloisField.card 2 n (by omega)))
  · obtain ⟨k,hk⟩ := hodd
    omega

/-- The non-natural case now requires an even field degree and an actual
Hermitian constituent, together with both original component kernels. -/
def OriginalNonseparatedEvenHermitianCase : Prop :=
  ∃ (t : G) (ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
    ∃ n : ℕ, 3 ≤ n ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n),
      ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
        D.seed ≤ centralizer (L : Set G)) ∧ OriginalEvenHermitianAnalysis D ht n e

/-- The literal original Hall consumer, with the natural/natural two-kernel
branch fully recognized and no constituent premise added. -/
theorem original_hall_conclusion_or_even_hermitian_analysis
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    (IsPGroup 3 B ∨ ∃ n : ℕ, Monoid.exponent B ∣ 2^n+1) ∨
      OriginalNonseparatedEvenHermitianCase D := by
  rcases original_hall_conclusion_or_nonseparated_even D c with hh |
      ⟨t,ht,htn,n,hn,e,hsep,_⟩
  · exact Or.inl hh
  · exact Or.inr ⟨t,ht,htn,n,hn,e,hsep,
      original_even_seed_natural_or_hermitian_kernel D c n hn e ht htn hsep⟩
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
