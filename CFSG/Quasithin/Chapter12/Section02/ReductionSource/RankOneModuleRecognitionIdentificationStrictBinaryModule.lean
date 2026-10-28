module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationStrictTransvections
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictBinaryModule

/-!
# The natural opposite-factor module on the whole reduced layer

The original Chapter12 source hypotheses construct the residual cubic and
apply the genuine G.2.3 module theorem to the original closure. The result
retains I, P, E, W and X, the literal quotient P/E and its S₃ action, and
both complementary factors in the natural tensor model. Displacement by
an element of U outside W maps X/E onto W/E with the stated kernel.

Source: Aschbacher--Smith, 6.2.17, printed pp.689--690, and 12.2.2(3d).
The remaining central-quotient rank calculation and classification are
owned by qt-d-1222-recognition-strict-elimination. LocalAnalysis is supplied
by qt-d-1222-rankone-recognition-identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement TensorProduct
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- The natural crossing section under the literal quotient map, constructed
from the whole reduced layer and its original Sylow subgroup. -/
theorem strict_reduced_crossing_binary_module
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L (wholeReduced T L) <
      sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L) :
    ∃ d ∈ strictCrossingResidual (T : Subgroup G) L (wholeReduced T L),
      d ∈ L ∧ orderOf d = 3 ∧ d ∉ centralizer ({z} : Set G) ∧
    let D := strictBinarySetup (T : Subgroup G) L (wholeReduced T L) z
    let W := sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ centralizer (ZS (T : Subgroup G) L (wholeReduced T L) : Set G)
    let X := strictCrossingGroup (T : Subgroup G) L (wholeReduced T L) z d
    D.U = sourceClosure (T : Subgroup G) L (wholeReduced T L) z ∧
    D.S₂ d = strictCrossingIntersection (T : Subgroup G) L (wholeReduced T L) z d ∧
    D.S d = D.I d ⊓ centralizer (ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ∧
    D.I d = strictCrossingResidual (T : Subgroup G) L (wholeReduced T L) ⊔ sourceClosure (T : Subgroup G) L (wholeReduced T L) z ∧
    D.S d = W ⊔ X ∧
    ∃ (e : (D.I d ⧸ pCore 2 (D.I d)) ≃* Equiv.Perm (Fin 3))
      (hN : ((D.S₂ d).subgroupOf (D.S d)).Normal),
      letI := hN
      ∃ hA : IsElementaryAbelian 2 (D.S d ⧸ (D.S₂ d).subgroupOf (D.S d)),
        letI := hA
        ∃ (σ : Representation (ZMod 2) (Equiv.Perm (Fin 3))
          (Additive (D.S d ⧸ (D.S₂ d).subgroupOf (D.S d))))
          (c : Representation.BinaryConjugationSection (D.I d) (D.S d) (D.S₂ d)
            (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (D.I d)))))),
          D.V ≤ D.S₂ d ∧ D.S₂ d ≤ D.S d ∧
          ((D.S₂ d).subgroupOf (D.I d)).Normal ∧
          ⁅D.S₂ d, D.I d⁆ ≤ D.V ∧ IsElementaryAbelian 2 (D.S₂ d) ∧
          (∀ s : D.S d, (c.coordinates s).toAdd =
            Additive.ofMul (QuotientGroup.mk' ((D.S₂ d).subgroupOf (D.S d)) s)) ∧
          Finite (InvertedCubicTensor.multiplicitySpace σ) ∧
          IsCompl (c.imageSpace W) (c.imageSpace X) ∧
          (∃ j : InvertedCubicTensor.multiplicitySpace σ ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2]
                Additive (D.S d ⧸ (D.S₂ d).subgroupOf (D.S d)),
              ∀ a v, j ((Representation.tprod (Representation.trivial (ZMod 2) (Equiv.Perm (Fin 3))
                  (InvertedCubicTensor.multiplicitySpace σ)) (BinaryPermutation.coreRepresentation (Fin 3))) a v) =
                σ a (j v)) ∧
          (∀ u : D.I d, (u : G) ∈ sourceClosure (T : Subgroup G) L (wholeReduced T L) z → (u : G) ∉ W →
            LinearMap.ker (σ (e (QuotientGroup.mk' (pCore 2 (D.I d)) u)) - (1 : Module.End (ZMod 2) (Additive (D.S d ⧸ (D.S₂ d).subgroupOf (D.S d))))) = c.imageSpace W ∧
            LinearMap.range (σ (e (QuotientGroup.mk' (pCore 2 (D.I d)) u)) - (1 : Module.End (ZMod 2) (Additive (D.S d ⧸ (D.S₂ d).subgroupOf (D.S d))))) = c.imageSpace W ∧
            (c.imageSpace X).map (σ (e (QuotientGroup.mk' (pCore 2 (D.I d)) u)) - (1 : Module.End (ZMod 2) (Additive (D.S d ⧸ (D.S₂ d).subgroupOf (D.S d))))) = c.imageSpace W) := by
  obtain ⟨d, hdres, hdL, _, _, hd3, hdH⟩ := strict_exists_crossing_cubic h611 hnatural hz horder
  exact ⟨d, hdres, hdL, hd3, hdH,
    A.strict_binary_crossing_module h611 hnatural hz horder hTH hstrict hdres hdH⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
