module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalTensorSmallActors
public import Theory.Representation.OrthogonalFourPlusMatrix.LargeActorsGeneral

/-!
# The original tensor actor and its complete kernel budget

The whole seed normalizer satisfies the H.1.1 rank/codimension gap through
its actual factor marking. For an original elementary subgroup preserving
the seed, that gap and its pointwise kernel consume additive parts of the
full fixed-codimension budget. The higher-Thompson application uses B.2.4
on the full image and retains this kernel; no faithful restriction to a
single component or equality of the seed and full module is assumed.
Source: Aschbacher--Smith H.1.1(2), 9.2.1 and 9.2.4,
printed pp.378,730, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 ChapterE
open Representation.BinaryOffender.NaturalTensor
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary
local instance (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The H.1.1 rank gap for the literal original seed normalizer. -/
theorem original_even_seed_normalizer_bounds
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (A : Subgroup (linearNormalizer (originalSeedAction D))) (hA : IsElementaryTwo A) :
    rank A ≤ 2*n ∧
      rank A+n ≤ fixedCodim (normalizerRepresentation (originalSeedAction D)) A+1 ∧
      (n+1 < rank A → 3*n ≤ fixedCodim (normalizerRepresentation (originalSeedAction D)) A) := by
  let := D.quasisimple
  let : IsQuasisimple SL(2,GaloisField 2 n) := IsQuasisimple.of_mulEquiv e
  obtain ⟨q,hq,_,_,_,σ,hi,_,hσ,α,⟨b⟩⟩ :=
    original_even_seed_natural_tensor D c n hn e ht htn hsep
  let a := b.trans (ClassicalOrthogonal.FourPlusMatrix.NaturalTensor.binaryTensorEquiv α)
  have himage : actionImage (originalSeedAction D) = actionImage σ := by
    rw [←hσ]
    ext z
    constructor
    · rintro ⟨g,rfl⟩; exact ⟨q g,Units.ext rfl⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨l,rfl⟩ := hq g
      exact ⟨l,Units.ext rfl⟩
  have hb := ClassicalOrthogonal.FourPlusMatrix.GeneralActors.marked_normalizer_bounds
    σ hi (Theory.PSL2.sl2_center_eq_bot _)
    (ClassicalOrthogonal.FourPlusMatrix.NaturalTensor.marking α)
    a.toLinearEquiv (fun g v => LinearMap.congr_fun (a.isIntertwining' g) v)
    n (by omega) (GaloisField.card 2 n (by omega))
  unfold normalizerRepresentation linearNormalizer at hb
  rw [←himage] at hb
  exact hb A hA

/-- The actual preserving actor retains its kernel's share of the full budget. -/
theorem original_even_preserving_seed_budget_gap
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (A : Subgroup D.maximalLocal) [IsElementaryAbelian 2 A]
    (hs : A.map D.maximalLocal.subtype ≤ normalizer (D.seed : Set G))
    (hmove : (originalPreservingSeedHom D A hs).range ≠ ⊥) :
    rank (originalPreservingSeedHom D A hs).range ≤ 2*n ∧
      fixedCodim ((originalFullAction D).comp A.subtype) (originalPreservingSeedHom D A hs).ker +
        rank (originalPreservingSeedHom D A hs).range + n ≤
          fixedCodim (automizerRepresentation D.fullModule)
            (A.map (originalFullAutomizerHom D)) + 1 ∧
      (n+1 < rank (originalPreservingSeedHom D A hs).range →
        fixedCodim ((originalFullAction D).comp A.subtype) (originalPreservingSeedHom D A hs).ker +
          3*n ≤ fixedCodim (automizerRepresentation D.fullModule)
            (A.map (originalFullAutomizerHom D))) := by
  let f := originalPreservingSeedHom D A hs
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective _ f.rangeRestrict_surjective
  obtain ⟨hr,hgap,hlarge⟩ := original_even_seed_normalizer_bounds D c n hn e ht htn hsep
    f.range ⟨hmove,inferInstance⟩
  have hb := original_preserving_seed_kernel_budget D A hs
  change fixedCodim ((originalFullAction D).comp A.subtype) f.ker +
    fixedCodim (normalizerRepresentation (originalSeedAction D)) f.range ≤ _ at hb
  dsimp only [f] at hr hgap hlarge hb
  refine ⟨hr,by omega,fun h => ?_⟩
  have hh := hlarge h
  omega

/-- A moving higher-Thompson actor's full rank pays for both the seed gap and
its entire pointwise seed kernel. This does not identify seed and full module. -/
theorem original_even_thompson_seed_budget_gap
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (j : ℕ) (A : Subgroup D.maximalLocal)
    (hA : A ∈ ChapterB.thompsonFamily ((T : Subgroup G).subgroupOf D.maximalLocal) j)
    (hne : A.map (originalFullAutomizerHom D) ≠ ⊥)
    (hs : A.map D.maximalLocal.subtype ≤ normalizer (D.seed : Set G))
    (hmove : (originalPreservingSeedHom D A hs).range ≠ ⊥) :
    fixedCodim ((originalFullAction D).comp A.subtype) (originalPreservingSeedHom D A hs).ker +
      rank (originalPreservingSeedHom D A hs).range + n ≤
        rank (A.map (originalFullAutomizerHom D)) + j + 1 := by
  let : IsElementaryAbelian 2 A := hA.2.1
  have hb := (original_even_preserving_seed_budget_gap D c n hn e ht htn hsep A hs hmove).2.1
  have hu := original_full_thompson_fixedCodim_bound D j A hA hne
  omega

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
