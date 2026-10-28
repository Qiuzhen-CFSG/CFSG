module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietSeedCubic
public import CFSG.Quasithin.ChapterD.Section03.EvenHermitianExclusion
public import Theory.Representation.OrthogonalFourPlusMatrix.LargeActorsGeneral

/-!
# Natural tensor recognition for the original quiet rank-one seed

The original seed descends faithfully to the marked SL₂ square, with full
kernel O₂(L₀). Its actual normalizer inherits the local cubic bound. The D.3
classification gives a natural tensor or two nonzero factor kernels with a
Hermitian constituent. The multiplicity cost excludes the latter, constructing
natural tensor coordinates on this very seed. These coordinates imply its
exact degree and the non-FF rank gap in the full seed normalizer.

The source application retains the alternative of nonzero component-fixed
support. Ambient exclusion of the natural tensor and the separate even-degree
fixed-layer assertion remain required; recognition alone does not prove them.
Source: Aschbacher--Smith D.3.7,3.2.6(1),H.1.1, pp.197--199,581,378.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.QuadraticFourGroup.TensorClassification
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 CentralHall.Nonlinear.Modules
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary
local instance (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2

/-- The unchanged seed with both literal component inclusions, its full action
kernel and actual natural-tensor intertwiner. -/
def QuietRankOneSeedMarking {n : ℕ}
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) : Prop :=
  ∃ q : localOrbit T L →* SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n),
    Function.Surjective q ∧ q.ker = pCore 2 (localOrbit T L) ∧
    (∀ l : L, q ⟨l,le_componentOrbit L T l.property⟩ = (e (QuotientGroup.mk' _ l),1)) ∧
    (∀ l : L, q (originalConjugateOrbitInclusion ht l) = (1,e (QuotientGroup.mk' _ l))) ∧
    ∃ σ : Representation (ZMod 2)
        (SL(2,GaloisField 2 n) × SL(2,GaloisField 2 n)) (Additive D.seed),
      σ.IsIrreducible ∧ Function.Injective σ ∧ σ.comp q = originalSeedAction D ∧
      (originalSeedAction D).ker = pCore 2 (localOrbit T L) ∧
      ∃ α : MulAut SL(2,GaloisField 2 n), Nonempty (σ.Equiv (restrictScalars (k := ZMod 2)
        (externalTensor
          ((SL2.BinarySmall.embeddedNatural (RingHom.id (GaloisField 2 n))).comp α.symm.toMonoidHom)
          (SL2.BinarySmall.embeddedNatural (RingHom.id (GaloisField 2 n))))))

/-- Quiet source hypotheses construct actual tensor coordinates whenever
neither original component centralizes the seed. No Hall context is used. -/
theorem quiet_rankOne_seed_marking_of_not_separated
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (n : ℕ) (hn3 : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) : QuietRankOneSeedMarking D e ht := by
  let := D.quasisimple
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_quotient_simple D hn
  let : IsSimpleGroup SL(2,GaloisField 2 n) := e.symm.isSimpleGroup
  let : IsQuasisimple SL(2,GaloisField 2 n) := IsQuasisimple.of_mulEquiv e
  let : FiniteDimensional (ZMod 2) (Additive D.seed) := Module.Finite.of_finite
  obtain ⟨q,hq,hk,hl,hr,σ,hi,hσ⟩ := quiet_seed_product_action D hmany hn hJ e ht htn
  have hf := original_seed_product_faithful_of_not_separated D e ht hsep q hl hr σ hσ
  have hkernel : (originalSeedAction D).ker = pCore 2 (localOrbit T L) := by
    rw [←hσ,MonoidHom.ker_comp_of_injective _ _ hf,hk]
  have himage : actionImage (originalSeedAction D) = actionImage σ := by
    rw [←hσ]
    ext x
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨q l,Units.ext rfl⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨l,rfl⟩ := hq g
      exact ⟨l,Units.ext rfl⟩
  have hsmall := quiet_seed_normalizer_cubic_of_not_separated D hmany hn hJ ht htn hsep
  have hsmallσ : cubicRatio (normalizerRepresentation σ) ≤ 2 := by
    unfold normalizerRepresentation linearNormalizer at hsmall ⊢
    rwa [himage] at hsmall
  have hSQ : IsSQTK KnownSimple.IsKnownSimple (L ⧸ pCore 2 L) := by
    have hlocal := (D.local_internal_module (source_module_nonsolvable_uniqueness D)).sqtk
    have hL : IsSQTK KnownSimple.IsKnownSimple L :=
      (IsSQTK.equiv (subgroupOfEquivOfLe
        ((le_componentOrbit L T).trans le_sup_left))).mp
        (hlocal.subgroup (L.subgroupOf (localJoin T L)))
    refine ⟨?_,hL.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hL.stronglyQuasithin p hp ho)
  have hS := IsSQTK.knownSimple_of_equiv e hSQ
  refine ⟨q,hq,hk,hl,hr,σ,hi,hf,hσ,hkernel,?_⟩
  rcases ChapterD.even_square_natural_or_hermitian_kernel σ hi hf hS hn3 hsmallσ with hnat | hherm
  · exact hnat
  · exact (ChapterD.not_even_square_hermitian_multiplicity σ hi hf hS
      (ChapterD.even_square_hermitian_multiplicity σ hi hf hherm)).elim

/-- The seed degree follows from its constructed intertwiner. -/
theorem quiet_rankOne_seed_finrank
    {n : ℕ} (hn : 3 ≤ n)
    {e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)}
    {t : G} {ht : t ∈ (T : Subgroup G)} (hm : QuietRankOneSeedMarking D e ht) :
    Module.finrank (ZMod 2) (Additive D.seed) = 4*n := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,⟨a⟩⟩ := hm
  exact a.toLinearEquiv.finrank_eq.trans
    (NaturalTensor.finrank_tensor (GaloisField 2 n) (GaloisField.card 2 n (by omega)))

/-- The full seed normalizer obeys H.1.1 with the exact original marking. -/
theorem quiet_rankOne_seed_normalizer_rank_gap
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {n : ℕ} (hn : 3 ≤ n)
    {e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)}
    {t : G} {ht : t ∈ (T : Subgroup G)} (hm : QuietRankOneSeedMarking D e ht) :
    ∀ A : Subgroup (linearNormalizer (originalSeedAction D)), IsElementaryTwo A →
      rank A ≤ 2*n ∧ rank A+n ≤ fixedCodim (normalizerRepresentation (originalSeedAction D)) A+1 ∧
      (n+1 < rank A → 3*n ≤ fixedCodim (normalizerRepresentation (originalSeedAction D)) A) := by
  let := D.quasisimple
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_quotient_simple D hnon
  let : IsQuasisimple SL(2,GaloisField 2 n) := IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup SL(2,GaloisField 2 n) := e.symm.isSimpleGroup
  obtain ⟨q,hq,_,_,_,σ,hi,_,hσ,_,α,⟨b⟩⟩ := hm
  let a := b.trans (ClassicalOrthogonal.FourPlusMatrix.NaturalTensor.binaryTensorEquiv α)
  have himage : actionImage (originalSeedAction D) = actionImage σ := by
    rw [←hσ]
    ext x
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨q l,Units.ext rfl⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨l,rfl⟩ := hq g
      exact ⟨l,Units.ext rfl⟩
  have hb : ∀ A : Subgroup (linearNormalizer σ), IsElementaryTwo A →
      rank A ≤ 2*n ∧ rank A+n ≤ fixedCodim (normalizerRepresentation σ) A+1 ∧
      (n+1 < rank A → 3*n ≤ fixedCodim (normalizerRepresentation σ) A) := by
    intro A hA
    exact ClassicalOrthogonal.FourPlusMatrix.GeneralActors.marked_normalizer_bounds σ hi
      center_eq_bot_of_simple_perfect (ClassicalOrthogonal.FourPlusMatrix.NaturalTensor.marking α)
      a.toLinearEquiv (fun g v => LinearMap.congr_fun (a.isIntertwining' g) v)
      n (by omega) (GaloisField.card 2 n (by omega)) A hA
  unfold normalizerRepresentation linearNormalizer at hb ⊢
  rwa [himage]

/-- In particular this actual seed is non-FF under its entire linear normalizer. -/
theorem quiet_rankOne_seed_normalizer_not_ff
    (hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {n : ℕ} (hn : 3 ≤ n)
    {e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)}
    {t : G} {ht : t ∈ (T : Subgroup G)} (hm : QuietRankOneSeedMarking D e ht) :
    ¬ IsFFModule (normalizerRepresentation (originalSeedAction D)) := by
  rintro ⟨A,hA,hbound⟩
  have hgap := (quiet_rankOne_seed_normalizer_rank_gap D hnon hn hm A hA).2.1
  omega

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
