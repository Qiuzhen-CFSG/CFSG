module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.ClassConstruction.FixedPoints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.NormalizerAction

/-!
# The fixed-vector branch lies in the marked centralizer

The actual A6 complement and orbit-stabilizer imply that N(E) is transitive
on the fifteen nonidentity elements of E. Conjugate a vector fixed by x to
the marked involution z. The same normalizer conjugator places x in C_G(z),
where the supplied equivalence k gives the original Case II coordinates.
Thus class coverage in this branch reduces to the finite centralizer model,
without replacing internal conjugacy by ambient fusion.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Lemma 6 and Section 5, pp.9–10.
-/

open Subgroup
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)

include L

public theorem normalizerHasFixedVector_iff_conjugate_centralizer
    (x : normalizer (CaseII.E D k : Set G)) :
    normalizerHasFixedVector D k x ↔
      ∃ t : TwistedModel, IsConj x (normalizerCentralizer D k t) := by
  constructor
  · rintro ⟨v, hv, hfix⟩
    obtain ⟨K, hK, ⟨eK⟩⟩ := L.normalizer_E
    have hcard : Nat.card (CaseII.eNormalizerQuotient D k) = 360 := by
      rw [Nat.card_congr (hK.symm.QuotientMulEquiv.trans eK).toEquiv,
        nat_card_alternatingGroup, Nat.card_fin]
      decide
    obtain ⟨g, hg⟩ := CaseII.E_fusion_of_quotient_card D k hcard v
      (CaseII.eNormalizerPoint D k) hv (CaseII.eNormalizerPoint_ne_one D k)
    let y := g * x * g⁻¹
    have hyC : (y : G) ∈ D.centralizer := by
      apply mem_centralizer_singleton_iff.mpr
      have hvx : (x : G) * v * (x : G)⁻¹ = (v : G) :=
        congrArg Subtype.val hfix
      change (g : G) * v * (g : G)⁻¹ = D.z at hg
      change ((g : G) * x * (g : G)⁻¹) * D.z =
        D.z * ((g : G) * x * (g : G)⁻¹)
      rw [← hg]
      have hc : (x : G) * v = (v : G) * x := mul_inv_eq_iff_eq_mul.mp hvx
      calc
        _ = (g : G) * ((x : G) * v) * (g : G)⁻¹ := by group
        _ = (g : G) * ((v : G) * x) * (g : G)⁻¹ := by rw [hc]
        _ = _ := by group
    obtain ⟨t, ht⟩ := k.surjective ⟨y, hyC⟩
    refine ⟨t, isConj_iff.mpr ⟨g, ?_⟩⟩
    exact Subtype.ext (congrArg Subtype.val ht).symm
  · rintro ⟨t, ht⟩
    exact (normalizerHasFixedVector_isConj D k ht).mpr
      (normalizerCentralizer_hasFixedVector D k t)

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
