module

public import Theory.GroupTheory.ZStar.CoreFree
public import Theory.GroupTheory.PPrimeCorePGroupQuotient
public import Theory.GroupTheory.PPrimeCoreReduction
public import Theory.GroupTheory.SylowCentralFusionWitness
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Z-star in faithful two-group extensions

If a two-group acts faithfully on a finite group with trivial odd core,
the semidirect product also has trivial odd core. A nonidentity actor is
not central in that product. Thus an involution among the actors, central
in a specified Sylow subgroup, has a distinct conjugate in that Sylow
subgroup by the core-free Z-star theorem.

The last theorem applies the elementary fusion input to this actual
semidirect product. The fusion input remains explicit; no existence
theorem for its local witnesses is asserted here.

Source: Glauberman, “On the automorphism group of a finite group having
no non-identity normal subgroups of odd order”, Math. Z. 93 (1966),
Theorem 1, pp.157–158, DOI 10.1007/BF01111033. These are the Z-star
steps common to the abelian-Sylow and normal-complement arguments.
-/

public section

namespace Glauberman.ZStar
open Subgroup SemidirectProduct

universe u
variable {G A : Type u} [Group G] [Group A]

/-- A two-group extension of an odd-core-free group has trivial odd core. -/
theorem semidirect_oddCore_eq_bot [Finite G] [Finite A]
    (φ : A →* MulAut G) (hG : pPrimeCore 2 G = ⊥) (hA : IsPGroup 2 A) :
    pPrimeCore 2 (G ⋊[φ] A) = ⊥ := by
  let : Finite (G ⋊[φ] A) := Finite.of_equiv (G × A) SemidirectProduct.equivProd.symm
  let N := (SemidirectProduct.rightHom : G ⋊[φ] A →* A).ker
  let eN : G ≃* N := (MonoidHom.ofInjective SemidirectProduct.inl_injective).trans
    (MulEquiv.subgroupCongr SemidirectProduct.range_inl_eq_ker_rightHom)
  have hN : pPrimeCore 2 N = ⊥ :=
    Theory.GroupTheory.pPrimeCore_eq_bot_of_equiv eN.symm hG
  apply pPrimeCore_eq_bot_of_isPGroup_quotient 2 N hN
  let e : (G ⋊[φ] A) ⧸ N ≃* A :=
    QuotientGroup.quotientKerEquivOfSurjective
      SemidirectProduct.rightHom SemidirectProduct.rightHom_surjective
  exact hA.of_equiv e.symm

private theorem actor_not_central (φ : A →* MulAut G) (hf : Function.Injective φ)
    {a : A} (ha : a ≠ 1) : (SemidirectProduct.inr a : G ⋊[φ] A) ∉ center _ := by
  intro hc
  apply ha
  apply hf
  apply MulEquiv.ext
  intro g
  have h := congrArg SemidirectProduct.left
    (mem_center_iff.mp hc (SemidirectProduct.inl g))
  simpa using h.symm

/-- A Sylow-central involution acting faithfully is not weakly closed.
The Sylow and its centrality are those in the literal semidirect product. -/
theorem exists_distinct_conjugate_in_faithful_two_action [Finite G] [Finite A]
    (φ : A →* MulAut G) (hf : Function.Injective φ)
    (hG : pPrimeCore 2 G = ⊥) (hA : IsPGroup 2 A)
    (T : Sylow 2 (G ⋊[φ] A)) (a : A)
    (ha : BenderSuzuki.PFAppendixIII.IsInvolution a)
    (haT : (inr a : G ⋊[φ] A) ∈ (T : Subgroup (G ⋊[φ] A)))
    (hc : ∀ t ∈ (T : Subgroup (G ⋊[φ] A)), t * inr a = inr a * t) :
    ∃ g : G ⋊[φ] A, g * inr a * g⁻¹ ∈ (T : Subgroup (G ⋊[φ] A)) ∧
      g * inr a * g⁻¹ ≠ inr a := by
  classical
  let : Finite (G ⋊[φ] A) := Finite.of_equiv (G × A) SemidirectProduct.equivProd.symm
  by_contra h
  push Not at h
  have hi : BenderSuzuki.PFAppendixIII.IsInvolution (inr a : G ⋊[φ] A) :=
    ⟨fun he => ha.ne_one (inr_injective (he.trans (map_one _).symm)),
      by simp only [← map_pow, ha.sq_eq_one, map_one]⟩
  exact actor_not_central φ hf ha.ne_one
    (glauberman_zstar_corefree (semidirect_oddCore_eq_bot φ hG hA)
      T (inr a) hi haT hc ⟨haT, h⟩)

/-- Discharge the nontrivial-fusion premise of the two elementary selections
in the faithful action used by Glauberman's automorphism proof. -/
theorem fusion_witnesses_in_faithful_two_action [Finite G] [Finite A]
    (fusion : SylowCentralFusion.CentralInvolutionFusion.{u})
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
  let : Finite (G ⋊[φ] A) := Finite.of_equiv (G × A) SemidirectProduct.equivProd.symm
  apply fusion (G ⋊[φ] A) T (inr a)
  · rw [orderOf_injective SemidirectProduct.inr SemidirectProduct.inr_injective]
    exact orderOf_eq_prime ha.sq_eq_one ha.ne_one
  · exact haT
  · exact hc
  · exact exists_distinct_conjugate_in_faithful_two_action φ hf hG hA T a ha haT hc

end Glauberman.ZStar
