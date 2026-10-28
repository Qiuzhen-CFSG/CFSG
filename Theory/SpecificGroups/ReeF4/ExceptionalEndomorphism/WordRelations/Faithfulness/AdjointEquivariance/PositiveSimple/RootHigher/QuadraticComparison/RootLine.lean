module
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootHigher.QuadraticComparison.Reduction
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootHigher.QuadraticComparison.Routes
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.RootSums.RootSpace
/-!
# The quadratic operator's characteristic-zero root weight

The identity `2J = [E,[E,R]]` puts the integral quadratic operator in Geck's
Lie algebra over an algebraic closure of the rationals. The Leibniz identity
gives weight `r + 2i`. When this is a root, the integral primitive-root-line
API gives an integer multiple of a Tits conjugate. Actual-route comparison
then identifies its line after specialization. Division by two occurs only
in characteristic zero.

Sources: Geck's construction in `IntegralGeckConstruction` and the integral
root-space/primitivity theorem `RootSums.RootSpace`.
-/

public section
open scoped Matrix
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
set_option backward.isDefEq.respectTransparency false
local notation "P₀" => scalarExtension (P := typeF4RootPairing) (b := typeF4RootPairing_base)
local notation "b₀" => scalarExtensionBase (P := typeF4RootPairing) (b := typeF4RootPairing_base)
local notation "K₀" => RatAlgClosure
set_option maxHeartbeats 800000

private lemma root_mem_weight (r : typeF4Roots) :
    (F4Chevalley.integralOperators.rootOperator r).map (algebraMap ℤ K₀) ∈
      RootPairing.GeckConstruction.lieAlgebra b₀ ∧
    HasRootWeight (P := P₀) (b := b₀) r
      ((F4Chevalley.integralOperators.rootOperator r).map (algebraMap ℤ K₀)) := by
  let z := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
  obtain ⟨ε, hε, h⟩ := integralRootOperator_eq_sign_transport r z.word z.simple z.target
  have hmat : F4Chevalley.integralOperators.rootOperator r =
      ε • titsConjugate (P := P₀) (b := b₀) z.word (eMatrix z.simple) := by
    rw [scalarExtension_eMatrix, scalarExtension_titsConjugate]
    exact h
  rw [hmat, Matrix.map_smul _ _ (map_zsmul _ _), ← Int.cast_smul_eq_zsmul K₀]
  constructor
  · apply (RootPairing.GeckConstruction.lieAlgebra b₀).smul_mem
    apply map_titsConjugate_mem_lieAlgebra
    rw [map_eMatrix]
    exact RootPairing.GeckConstruction.e_mem_lieAlgebra (P := P₀) (b := b₀) z.simple
  · have hw := map_titsConjugate_hasRootWeight (P := P₀) (b := b₀) z.word z.simple
    rw [scalarExtension_reflectionWord, z.target] at hw
    intro l
    rw [lie_smul, hw l, smul_comm]

/-- The characteristic-zero image of the quadratic operator lies in Geck's Lie
algebra and has the sum weight `r + 2i`, whether or not that weight is a root. -/
lemma integralQuadraticOperator_mem_weight (i : typeF4RootPairing_base.support)
    (r : typeF4Roots) :
    let J : Matrix ((b₀).support ⊕ typeF4Roots) ((b₀).support ⊕ typeF4Roots) K₀ :=
      (integralQuadraticOperator i r).map (algebraMap ℤ K₀)
    J ∈ RootPairing.GeckConstruction.lieAlgebra b₀ ∧
    ∀ l : (b₀).support,
      ⁅RootPairing.GeckConstruction.h (P := P₀) (b := b₀) l, J⁆ =
      ((P₀).pairing r l + 2 * (P₀).pairing i l) • J := by
  let E : Matrix ((b₀).support ⊕ typeF4Roots) ((b₀).support ⊕ typeF4Roots) K₀ := (eMatrix (P := typeF4RootPairing) i).map (algebraMap ℤ K₀)
  let R : Matrix ((b₀).support ⊕ typeF4Roots) ((b₀).support ⊕ typeF4Roots) K₀ := (F4Chevalley.integralOperators.rootOperator r).map (algebraMap ℤ K₀)
  let J : Matrix ((b₀).support ⊕ typeF4Roots) ((b₀).support ⊕ typeF4Roots) K₀ := (integralQuadraticOperator i r).map (algebraMap ℤ K₀)
  have hE : E = (F4Chevalley.integralOperators.rootOperator i).map (algebraMap ℤ K₀) := by
    dsimp only [E]
    congr 1
    exact (rootOperator_simple (P := typeF4RootPairing) i).symm
  obtain ⟨hEmem, hEweight⟩ := root_mem_weight (i : typeF4Roots)
  rw [← hE] at hEmem hEweight
  obtain ⟨hRmem, hRweight⟩ := root_mem_weight r
  change R ∈ _ at hRmem
  change HasRootWeight (P := P₀) (b := b₀) r R at hRweight
  have hdouble : (2 : K₀) • J = ⁅E, ⁅E, R⁆⁆ := by
    have h := congrArg (fun A : Matrix Coordinate Coordinate ℤ => A.map (algebraMap ℤ K₀))
      (integralQuadraticOperator_two_smul i r)
    simpa only [Matrix.map_smul _ _ (map_zsmul _ _),
      ← Int.cast_smul_eq_zsmul K₀, Int.cast_ofNat, Matrix.map_sub _ (map_sub _),
      Matrix.map_mul, Ring.lie_def] using h
  have hhalf : J = (2 : K₀)⁻¹ • ⁅E, ⁅E, R⁆⁆ := by
    rw [← hdouble, inv_smul_smul₀ (by norm_num : (2 : K₀) ≠ 0)]
  change J ∈ _ ∧ _
  constructor
  · rw [hhalf]
    apply (RootPairing.GeckConstruction.lieAlgebra b₀).smul_mem
    exact (RootPairing.GeckConstruction.lieAlgebra b₀).lie_mem hEmem
      ((RootPairing.GeckConstruction.lieAlgebra b₀).lie_mem hEmem hRmem)
  · intro l
    change ⁅_, J⁆ = _ • J
    rw [hhalf]
    rw [lie_smul, leibniz_lie,
      leibniz_lie (RootPairing.GeckConstruction.h (P := P₀) (b := b₀) l) E R]
    simp only [hEweight l, hRweight l, smul_lie,
      lie_smul, ← add_smul, smul_smul]
    congr 1
    ring

lemma integralQuadraticOperator_map_mem_root_line (m : ℕ) (i : typeF4RootPairing_base.support)
    (r k : typeF4Roots)
    (hk : typeF4RootPairing.root k =
      typeF4RootPairing.root r + (2 : ℕ) • typeF4RootPairing.root i) :
    ∃ c : CoefficientField m,
      (integralQuadraticOperator i r).map (Int.castRingHom (CoefficientField m)) =
        c • coordinateOperator m (Sum.inr k) := by
  let z := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) k
  obtain ⟨hmem, hweight⟩ := integralQuadraticOperator_mem_weight i r
  have hroot : (P₀).root k = (P₀).root r + (2 : ℕ) • (P₀).root i := by
    have hs : typeF4RootPairing.rootSpanMem ℤ k =
        typeF4RootPairing.rootSpanMem ℤ r + (2 : ℕ) • typeF4RootPairing.rootSpanMem ℤ i :=
      Subtype.ext hk
    change scalarExtensionRoot (P := typeF4RootPairing) (b := typeF4RootPairing_base) k =
      scalarExtensionRoot (P := typeF4RootPairing) (b := typeF4RootPairing_base) r +
        (2 : ℕ) • scalarExtensionRoot (P := typeF4RootPairing) (b := typeF4RootPairing_base) i
    ext l
    simp only [scalarExtensionRoot, hs, map_add, map_nsmul, Finsupp.add_apply,
      Finsupp.smul_apply, Pi.add_apply, Pi.smul_apply]
  have hp (l : typeF4RootPairing_base.support) :
      (P₀).pairing k l = (P₀).pairing r l + 2 * (P₀).pairing i l := by
    change (P₀).coroot' l ((P₀).root k) = _
    rw [hroot, map_add, map_nsmul]
    simp only [RootPairing.root_coroot'_eq_pairing, two_smul, two_mul]
  have hw : HasRootWeight (P := P₀) (b := b₀) (reflectionWord (P := P₀) (b := b₀) z.word z.simple)
      ((integralQuadraticOperator i r).map (algebraMap ℤ K₀)) := by
    rw [scalarExtension_reflectionWord, z.target]
    intro l
    rw [hp]
    exact hweight l
  obtain ⟨n, hn⟩ := RootSumSpace.integral_matrix_eq_smul_titsConjugate_of_weight
    (P := P₀) (b := b₀) (integralQuadraticOperator i r) z.word z.simple hmem hw
  rw [scalarExtension_eMatrix, scalarExtension_titsConjugate] at hn
  refine ⟨n, ?_⟩
  rw [hn, Matrix.map_smul _ _ (map_zsmul _ _), ← Int.cast_smul_eq_zsmul (CoefficientField m),
    coordinateOperator_eq_transport m k z.word z.simple z.target]
  rfl
end
end ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
