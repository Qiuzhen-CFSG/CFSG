module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalProductQuotient
public import CFSG.Quasithin.Chapter10.SourceA5TensorRecognition

/-!
# Tensor recognition with the original marked product quotient

The product quotient is constructed from the original nonnormal A₅ component
and the chosen conjugating element. Relabelling its two factors through a
specified A₅–PSL₂(4) equivalence discharges the quotient, surjectivity, kernel,
and first-factor marking premises of determinant recognition. The actual
binary section and cubic fixed-point-freeness remain explicit source inputs.

Source: Aschbacher–Smith D.3.7 and 3.2.6, printed pp.197–199 and581.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open Representation.QuadraticFourGroup Representation.QuadraticFourGroup.TensorClassification
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
  (j : alternatingGroup (Fin 5) ≃* Factor 2)

/-- The original product quotient in the two projective-linear coordinates. -/
def originalA5FactorProjection : localOrbit T L →* Factor 2 × Factor 2 :=
  (j.prodCongr j).toMonoidHom.comp (originalA5ProductProjection D e hn ht htn)

/-- Relabelling preserves surjectivity of the original product quotient. -/
theorem originalA5FactorProjection_surjective :
    Function.Surjective (originalA5FactorProjection D e hn ht htn j) :=
  (j.prodCongr j).surjective.comp (originalA5ProductProjection_surjective D e hn ht htn)

/-- Relabelling retains the intrinsic two-core kernel. -/
theorem originalA5FactorProjection_ker :
    (originalA5FactorProjection D e hn ht htn j).ker = pCore 2 (localOrbit T L) := by
  rw [originalA5FactorProjection, MonoidHom.ker_comp_of_injective _ _
    (j.prodCongr j).injective, originalA5ProductProjection_ker]

/-- The original first-factor marking after the prescribed relabelling. -/
theorem originalA5FactorProjection_first (l : L) :
    originalA5FactorProjection D e hn ht htn j ⟨l,le_componentOrbit L T l.property⟩ =
      (j (e (QuotientGroup.mk' _ l)),1) := by
  change (j.prodCongr j) (originalA5ProductProjection D e hn ht htn _) = _
  rw [originalA5ProductProjection_first]
  exact Prod.ext rfl j.map_one

/-- The conjugate-factor marking after the same relabelling. -/
theorem originalA5FactorProjection_second (l : L) :
    originalA5FactorProjection D e hn ht htn j (originalConjugateOrbitInclusion ht l) =
      (1,j (e (QuotientGroup.mk' _ l))) := by
  change (j.prodCongr j) (originalA5ProductProjection D e hn ht htn _) = _
  rw [originalA5ProductProjection_second]
  exact Prod.ext j.map_one rfl

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- The original cubic-free section supplies the determinant model with no
independent product quotient or marking hypotheses. -/
theorem source_a5_tensor_model_of_original_cubic_free_product
    (hminimal : D.IsMinimalFullModule)
    (hseed : D.seed = D.fullModule) (hmodule : D.moduleSubgroup = D.fullModule)
    (σ : Representation (ZMod 2) (Factor 2 × Factor 2) W)
    (hfree : CubicFreeOnFactors σ)
    (s : BinaryConjugationSection (localOrbit T L) D.fullModule ⊥
      (σ.comp (originalA5FactorProjection D e hn ht htn j))) :
    Nonempty (SourceA5TensorModel D e) :=
  source_a5_tensor_model_of_cubic_free_product D e hminimal hseed hmodule
    (originalA5FactorProjection D e hn ht htn j)
    (originalA5FactorProjection_surjective D e hn ht htn j)
    (originalA5FactorProjection_ker D e hn ht htn j) j
    (originalA5FactorProjection_first D e hn ht htn j) σ hfree s

/-- The same original quotient also discharges the product premises for a
cubic-free central quotient of the source section. -/
theorem source_a5_tensor_model_of_original_cubic_free_cover
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (hminimal : D.IsMinimalFullModule)
    (hseed : D.seed = D.fullModule) (hmodule : D.moduleSubgroup = D.fullModule)
    (τ : Representation (ZMod 2) (Factor 2 × Factor 2) U)
    (σ : Representation (ZMod 2) (Factor 2 × Factor 2) W)
    (p : τ.IntertwiningMap σ) (hp : OneCohomology.IsCover p)
    (hfree : CubicFreeOnFactors σ)
    (s : BinaryConjugationSection (localOrbit T L) D.fullModule ⊥
      (τ.comp (originalA5FactorProjection D e hn ht htn j))) :
    Nonempty (SourceA5TensorModel D e) :=
  source_a5_tensor_model_of_cubic_free_cover D e hminimal hseed hmodule
    (originalA5FactorProjection D e hn ht htn j)
    (originalA5FactorProjection_surjective D e hn ht htn j)
    (originalA5FactorProjection_ker D e hn ht htn j) j
    (originalA5FactorProjection_first D e hn ht htn j) τ σ p hp hfree s

end CFSG.Quasithin.Chapter10
