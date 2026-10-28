module

public import Theory.GroupTheory.SylowCentralFusion
public import Theory.GroupTheory.ZStar.SylowAutomorphismAction

/-!
# The fusion selections in a faithful two-group action

Z-star supplies a distinct conjugate in the literal semidirect product used
in Glauberman's automorphism theorem. The completed fusion theorem supplies
both witnesses, discharging the fusion premise of the original consumer.

Source: Glauberman, Math. Z. 93 (1966), Lemma 1 and Theorem 1,
pp.155–158, DOI 10.1007/BF01111033. The original conditional consumer is
preserved in `ZStar.SylowAutomorphismAction`.
-/

public section
namespace Glauberman.ZStar
open Subgroup SemidirectProduct
universe u
variable {G A : Type u} [Group G] [Group A]

/-- The center-containing selection in the faithful action used in the
abelian-Sylow part of Glauberman's automorphism theorem. -/
theorem center_fusion_witness_in_faithful_two_action [Finite G] [Finite A]
    (φ : A →* MulAut G) (hf : Function.Injective φ)
    (hG : pPrimeCore 2 G = ⊥) (hA : IsPGroup 2 A)
    (T : Sylow 2 (G ⋊[φ] A)) (a : A)
    (ha : BenderSuzuki.PFAppendixIII.IsInvolution a)
    (haT : (inr a : G ⋊[φ] A) ∈ (T : Subgroup (G ⋊[φ] A)))
    (hc : ∀ t ∈ (T : Subgroup (G ⋊[φ] A)), t * inr a = inr a * t) :
    ∃ w : SylowCentralFusion.Witness T (inr a),
      (center T).map (T : Subgroup (G ⋊[φ] A)).subtype ≤ w.subgroup := by
  let : Finite (G ⋊[φ] A) := Finite.of_equiv (G × A) SemidirectProduct.equivProd.symm
  exact SylowCentralFusion.exists_center_witness T (inr a) haT hc
    (exists_distinct_conjugate_in_faithful_two_action φ hf hG hA T a ha haT hc)

/-- The literal existing consumer specialized to an explicit noncentral
normal-closure selection. Retained for compatibility with conditional callers. -/
theorem fusion_witnesses_in_faithful_two_action_of_noncentral_selection
    [Finite G] [Finite A]
    (noncentral : SylowCentralFusion.NoncentralNormalClosureSelection.{u})
    (φ : A →* MulAut G) (hf : Function.Injective φ)
    (hG : pPrimeCore 2 G = ⊥) (hA : IsPGroup 2 A)
    (T : Sylow 2 (G ⋊[φ] A)) (a : A)
    (ha : BenderSuzuki.PFAppendixIII.IsInvolution a)
    (haT : (inr a : G ⋊[φ] A) ∈ (T : Subgroup (G ⋊[φ] A)))
    (hc : ∀ t ∈ (T : Subgroup (G ⋊[φ] A)), t * inr a = inr a * t) :
    (∃ w : SylowCentralFusion.Witness T (inr a),
      (center T).map (T : Subgroup (G ⋊[φ] A)).subtype ≤ w.subgroup) ∧
    (∃ w : SylowCentralFusion.Witness T (inr a),
      w.subgroup ≤ normalClosure ({inr a} : Set (G ⋊[φ] A))) := by
  exact fusion_witnesses_in_faithful_two_action
    (SylowCentralFusion.centralInvolutionFusion_of_noncentralNormalClosureSelection noncentral)
    φ hf hG hA T a ha haT hc

/-- Both fusion selections in the faithful action used in Glauberman's
automorphism theorem, with the elementary fusion premise discharged. -/
theorem exists_fusion_witnesses_in_faithful_two_action [Finite G] [Finite A]
    (φ : A →* MulAut G) (hf : Function.Injective φ)
    (hG : pPrimeCore 2 G = ⊥) (hA : IsPGroup 2 A)
    (T : Sylow 2 (G ⋊[φ] A)) (a : A)
    (ha : BenderSuzuki.PFAppendixIII.IsInvolution a)
    (haT : (inr a : G ⋊[φ] A) ∈ (T : Subgroup (G ⋊[φ] A)))
    (hc : ∀ t ∈ (T : Subgroup (G ⋊[φ] A)), t * inr a = inr a * t) :
    (∃ w : SylowCentralFusion.Witness T (inr a),
      (center T).map (T : Subgroup (G ⋊[φ] A)).subtype ≤ w.subgroup) ∧
    (∃ w : SylowCentralFusion.Witness T (inr a),
      w.subgroup ≤ normalClosure ({inr a} : Set (G ⋊[φ] A))) := by
  exact fusion_witnesses_in_faithful_two_action SylowCentralFusion.centralInvolutionFusion
    φ hf hG hA T a ha haT hc

end Glauberman.ZStar
