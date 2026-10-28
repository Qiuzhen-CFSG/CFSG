module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalTensorBranch.Recognition
public import CFSG.Quasithin.Chapter10.SourceA5OriginalProductEmbedding
public import CFSG.Quasithin.Chapter10.SourceA5OriginalProductExchange
/-!
# The original same-seed A₅ tensor branch

The nonnormal component supplies its literal marked A₅ × A₅ quotient and
normal embedding in the full faithful actor. A Sylow element outside the
component normalizer exchanges the two factors with the twist induced by
its square. Recognition constructs the determinant tensor model from this
actual product action, minimality, the seed equality and the genuine cubic
bound; there are no auxiliary representation or central-cover premises.

This is the same-seed branch of Aschbacher–Smith D.3.7, printed pp.197–199.
The separate arguments proving the seed equality are not part of this branch.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original minimal full module is the marked determinant tensor whenever
its chosen seed is already the full module and its actual cubic ratio is at most two. -/
theorem source_a5_original_tensor_model_of_seed_eq_full
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hminimal : D.IsMinimalFullModule) (hseed : D.seed = D.fullModule)
    (hbound : SourceFullModuleCubicBound D) :
    Nonempty (SourceA5TensorModel D e) := by
  obtain ⟨t, ht, htn⟩ := SetLike.not_le_iff_exists.mp hn
  let U := D.fullModule.subgroupOf D.maximalLocal
  let := (source_full_module_reduced D).normal
  let qM := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
  let q := originalA5ProductProjection D e hn ht htn
  have hq := originalA5ProductProjection_surjective D e hn ht htn
  obtain ⟨i, hi, hinormal, hcompat⟩ := source_a5_original_product_embedding D e hn ht htn
  apply source_a5_tensor_model_of_canonical_product D e hminimal hseed hbound q hq
    (originalA5ProductProjection_ker D e hn ht htn)
    (originalA5ProductProjection_first D e hn ht htn) i hi hinormal hcompat
    ⟨t, le_normalizer_componentOrbit L T ht⟩ (originalA5ConjugationTwist D e hn ht)
  intro g
  obtain ⟨x, rfl⟩ := hq g
  rw [← originalA5ProductProjection_conjugate D e hn ht htn x, hcompat, hcompat]
  change qM ⟨t, _⟩ * qM ⟨x, _⟩ * (qM ⟨t, _⟩)⁻¹ = qM _
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

end CFSG.Quasithin.Chapter10
