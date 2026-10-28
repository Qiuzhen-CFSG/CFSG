module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.OriginalOddSeparation
public import CFSG.Quasithin.ChapterD.Section03.EvenTensor

/-!
# Even-linear analysis on the unchanged central Hall seed

The genuine component catalogue and the completed Suzuki, Janko and odd-prime
exclusions leave an actual binary SL2 quotient when separation fails. The
original non-A5 hypothesis makes its field degree at least three. The literal
orbit quotient, including both component restrictions and its two-core kernel,
descends the unchanged seed to a faithful irreducible square action.

The actual cubic bound then constructs a natural or Hermitian constituent in
one factor orientation, or a twisted exchanging involution in a small actor
of rank at most one plus the field degree. No actor lift or Schur linearity is
assumed. This applies to the original Hall Context and is re-exported through
the literal Hall source consumer.

The remaining even-linear tensor exclusion, constituent minimality and final
SeedAnalysisAt/SourceNonnormalCentralHallAt assembly remain with
qt-d-10-nona5-central-hall-orders. None is asserted here.
Source: Aschbacher--Smith D.3.7,3.2.6 and10.1.1,
printed pp.197--199,581,741.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance originalEvenElementary : IsElementaryAbelian 2 D.seed := D.seed_elementary
local instance originalEvenGaloisAlgebra (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) :=
  ZMod.algebra _ 2

/-- The original non-A₅ hypothesis removes the field-four endpoint. -/
theorem original_even_parameter_ge_three
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {n : ℕ} (hn : 2 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)) : 3 ≤ n := by
  have hne : n ≠ 2 := by
    intro he
    subst n
    exact c.not_a5 ⟨e.trans ((Theory.PSL2.sl2QuotientEquiv _).trans
      Atlas.Comparisons.Exceptional.psl2FourEquivAlt5)⟩
  omega

/-- The constituent/exchange conclusion on the original seed, with the
surjective orbit quotient and its two component restrictions recorded exactly. -/
def OriginalEvenSeedAnalysis {t : G} (ht : t ∈ (T : Subgroup G)) (n : ℕ)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)) : Prop :=
    ∃ q : localOrbit T L →* SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n),
      Function.Surjective q ∧ q.ker = pCore 2 (localOrbit T L) ∧
      (∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ = (e (QuotientGroup.mk' _ l),1)) ∧
      (∀ l : L, q (originalConjugateOrbitInclusion ht l) = (1,e (QuotientGroup.mk' _ l))) ∧
      ∃ σ : Representation (ZMod 2)
          (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) (Additive D.seed),
        σ.IsIrreducible ∧ Function.Injective σ ∧ σ.comp q = originalSeedAction D ∧
        ChapterD.EvenSquareAnalysis σ n

/-- The original nonseparated even-linear seed has either a natural/Hermitian
constituent in one of its actual factor restrictions, or a small cubic actor
moving one of its actual factor images. All quotient maps and both orientations
are retained on the unchanged seed. -/
theorem original_even_seed_constituent_or_exchange
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 2 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    OriginalEvenSeedAnalysis D ht n e := by
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
  exact ⟨q,hq,hker,hl,hr,σ,hi,hf,hσ,
    ChapterD.even_square_constituent_or_exchange σ hi hf
      (IsSQTK.knownSimple_of_equiv e (original_component_quotient_sqtk D)) n hn
      (GaloisField.card 2 n (by omega)) hsmallσ⟩

/-- The exhaustive source catalogue reduces any failure of separation to an
actual even-linear marking of degree at least three, with the constituent or
exchange analysis above. No model is imposed as an additional source premise. -/
theorem original_nonseparated_even_marking
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    ∃ n : ℕ, 3 ≤ n ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)) := by
  obtain ⟨n,hn,F,_,_,hF,⟨e⟩⟩ := original_nonseparated_model_even D c hnot ht htn hsep
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  let f : F ≃+* GaloisField 2 n := FiniteField.ringEquivOfCardEq (by
    simpa only [Fintype.card_eq_nat_card] using hF.trans (GaloisField.card 2 n (by omega)).symm)
  let a := (e.trans (Atlas.fieldEquivPSL 2 f)).trans (Theory.PSL2.sl2QuotientEquiv _).symm
  exact ⟨n,original_even_parameter_ge_three D c hn a,⟨a⟩⟩

/-- The original source hypotheses supply the complete even-linear constituent
or twisted-exchange alternative whenever seed separation fails. -/
theorem original_nonseparated_even_analysis
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    ∃ (n : ℕ), 3 ≤ n ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n),
      OriginalEvenSeedAnalysis D ht n e := by
  obtain ⟨n,hn,⟨e⟩⟩ := original_nonseparated_even_marking D c hnot ht htn hsep
  exact ⟨n,hn,e,original_even_seed_constituent_or_exchange D c n (by omega) e ht htn hsep⟩

/-- The actual odd Hall subgroup has the desired exponent, unless the original
seed has one of the concrete even-linear tensor configurations just constructed.
Moved minimality and exclusion of these configurations remain with the final
source assembly owner; neither is hidden in a model tag or a source callback. -/
theorem hall_exponent_or_even_analysis_of_moved_minimal
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    (hmin : MovedMinimal D) :
    (∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2^n+1) ∨
      ∃ (t : G) (ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
        ∃ n : ℕ, 3 ≤ n ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n),
          OriginalEvenSeedAnalysis D ht n e := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  by_cases hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)
  · exact Or.inl (hall_exponent_of_moved_minimal_and_crossed T D c hnot ht htn hmin
      (full_moved_centralizes_opposite_of_seed_separated D ht htn hsep))
  · exact Or.inr ⟨t,ht,htn,original_nonseparated_even_analysis D c hnot ht htn hsep⟩
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
