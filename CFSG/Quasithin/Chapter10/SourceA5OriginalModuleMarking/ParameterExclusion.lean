module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.LocalParameters
public import CFSG.Quasithin.Chapter10.SourceA5WeakClosureFixedSpace

/-!
# The original A₅ offender parameter contradictions

The source fixed-space identity (*) places the actual image of V₁ᵍ∩M in
the (4-k)-th family of the full Aut_M(V₁) action. The original local bounds
then exclude corank at most one in either chosen A₅ branch, and corank at
most two in the deleted-permutation branch. No smaller actor is substituted.
Normalization, nontriviality and (*) retain their separate geometric producer;
the parameter inequalities and numerical contradictions are discharged here.
Source: Aschbacher–Smith, 10.2.12, printed pp.754–755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The full local rank bound contradicts the original corank-at-most-one offender. -/
theorem source_a5_original_offender_corank_one_excluded
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hNL : D.maximalLocal ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤
      normalizer (L : Set G))
    (g : G) {k : ℕ} (hk : k ≤ 1)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ k) :
    let W := ⁅D.fullModule,L⁆
    let A := W.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal
    let C := centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)
    A ≤ normalizer (W : Set G) → ¬ A ≤ centralizer (W : Set G) →
    (∀ a ∈ A, a ∉ C → W ⊓ centralizer ({a} : Set G) ≤ centralizer (A : Set G)) →
    False := by
  dsimp only
  intro hAN ha hfix
  have hlo := source_a5_offender_local_moduleA_lower D e g (by omega : k ≤ 2)
    hsmall hAN ha hfix
  have hhi := source_a5_original_local_moduleA_le_two D e hi hNL
  have h : (4-k : ℕ) ≤ 2 := by exact_mod_cast hlo.trans hhi
  omega

/-- The deleted-module bound contradicts the actual corank-at-most-two offender. -/
theorem source_a5_original_deleted_offender_corank_two_excluded
    (f : alternatingGroup (Fin 5) ≃* alternatingGroup (Fin 5))
    (c : Representation.BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      (Representation.OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (hNL : D.maximalLocal ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤
      normalizer (L : Set G))
    (g : G) {k : ℕ} (hk : k ≤ 2)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ k) :
    let W := ⁅D.fullModule,L⁆
    let A := W.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal
    let C := centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)
    A ≤ normalizer (W : Set G) → ¬ A ≤ centralizer (W : Set G) →
    (∀ a ∈ A, a ∉ C → W ⊓ centralizer ({a} : Set G) ≤ centralizer (A : Set G)) →
    False := by
  dsimp only
  intro hAN ha hfix
  have hlo := source_a5_offender_local_moduleA_lower D e g hk hsmall hAN ha hfix
  have hhi := source_a5_original_local_moduleA_le_one_of_deleted D e f c hNL
  have h : (4-k : ℕ) ≤ 1 := by exact_mod_cast hlo.trans hhi
  omega

end CFSG.Quasithin.Chapter10
