module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.TwistedTensor.Rank
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.TwistedTensor.Overgroup
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.TwistedTensor.ScalarExtension
public import Theory.ElementaryAbelian.Basic

/-!
# The L₂(8) twisted tensor exclusion in 6.2.19

Let F*(H) be identified with the actual PSL₂(8) matrix quotient, and let the
binary representation, restricted to this subgroup and extended to F₈, be
intertwined with `N ⊗ N^σ ⊗ N^(σ²)`. Every ambient involution lies in F*(H),
and its displacement has rank four over both F₈ and F₂. Consequently no element
of an elementary abelian two-subgroup X has displacement rank two.

The input retains the group isomorphism and scalar-extension intertwiner.
No involution-containment or rank premise is assumed. The rank calculation works
for every specified field automorphism, so in particular for either generator
of Gal(F₈/F₂). Mathlib places the extended coefficient field on the left of the
tensor product; this is the usual scalar extension in the source. The displayed
eight-dimensionality follows from the actual tensor model and is not an extra
assumption needed by the proof. The canonical Frobenius model is covered too.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, G.11.2(11),
printed p.364 (PDF p.375), and its exclusion in the proof of 6.2.19,
printed p.691 (PDF p.708). Exhaustivity of the G.11 catalogue is not used.
-/

public noncomputable section

open scoped MatrixGroups TensorProduct

namespace Representation.RankTwo.TwistedTensor

open Theory.GroupTheory Subgroup Representation.SL2.BinarySmall

local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

set_option backward.isDefEq.respectTransparency false in
/-- The rank four calculation descends through the actual scalar-extension
intertwiner; no numerical rank hypothesis is needed. -/
theorem rank_eq_four_of_isTriple (ρ : Representation (ZMod 2) SL(2,F) V)
    (h : IsTriple ρ) (g : SL(2,F)) (hg : orderOf g = 2) :
    Module.finrank (ZMod 2) (movedSpace ρ g) = 4 := by
  obtain ⟨f⟩ := h
  have he := finrank_movedSpace_equiv (k := F) (V := F ⊗[ZMod 2] V)
    (W := TripleSpace F) (extendScalars F ρ) (triple (K := F)) f g
  exact (finrank_movedSpace_extendScalars (E := F) ρ g).symm.trans
    (he.trans (rank_eq_four g hg))

set_option backward.isDefEq.respectTransparency false in
/-- Descent for a specified field automorphism, including either Galois generator. -/
theorem rank_eq_four_of_model (σ : F ≃+* F)
    (ρ : Representation (ZMod 2) SL(2,F) V)
    (h : Nonempty ((extendScalars F ρ).Equiv (twistedTriple σ)))
    (g : SL(2,F)) (hg : orderOf g = 2) :
    Module.finrank (ZMod 2) (movedSpace ρ g) = 4 := by
  obtain ⟨f⟩ := h
  have he := finrank_movedSpace_equiv (k := F) (V := F ⊗[ZMod 2] V)
    (W := TripleSpace F) (extendScalars F ρ) (twistedTriple σ) f g
  exact (finrank_movedSpace_extendScalars (E := F) ρ g).symm.trans
    (he.trans (twisted_rank_eq_four σ g hg))

variable {H : Type*} [Group H] [Finite H]

set_option backward.isDefEq.respectTransparency false in
/-- Source case (11), with the actual marked SL₂(8) component and the specified
scalar-extension equivalence. Every ambient involution has rank four. -/
theorem ambient_rank_eq_four (σ : F ≃+* F) (ρ : Representation (ZMod 2) H V)
    (e : generalizedFitting H ≃* SL(2,F))
    (h : Nonempty ((extendScalars F
      ((ρ.comp (generalizedFitting H).subtype).comp e.symm.toMonoidHom)).Equiv
        (twistedTriple σ)))
    (g : H) (hg : orderOf g = 2) :
    Module.finrank (ZMod 2) (movedSpace ρ g) = 4 := by
  have hpow : g ^ 2 = 1 := by simpa only [hg] using pow_orderOf_eq_one g
  have hmem := involution_mem_generalizedFitting e g hpow
  let x : generalizedFitting H := ⟨g, hmem⟩
  have hx : orderOf (e x) = 2 := by
    rw [e.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hg
  have hr := rank_eq_four_of_model σ
    ((ρ.comp (generalizedFitting H).subtype).comp e.symm.toMonoidHom) h (e x) hx
  change Module.finrank (ZMod 2) (movedSpace ρ ((e.symm (e x)) : H)) = 4 at hr
  rw [e.symm_apply_apply] at hr
  exact hr


/-- PSL₂ uses the literal central quotient: its characteristic-two quotient
isomorphism is composed with the supplied source group identification. -/
theorem case_eleven_rank_eq_four (σ : F ≃+* F) (ρ : Representation (ZMod 2) H V)
    (e : generalizedFitting H ≃* PSL(2,F))
    (h : Nonempty ((extendScalars F ((ρ.comp (generalizedFitting H).subtype).comp
      (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm).symm.toMonoidHom)).Equiv
        (twistedTriple σ)))
    (g : H) (hg : orderOf g = 2) :
    Module.finrank (ZMod 2) (movedSpace ρ g) = 4 :=
  ambient_rank_eq_four σ ρ (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm) h g hg

set_option backward.isDefEq.respectTransparency false in
/-- The exact X input for 6.2.19 is elementary abelian of exponent two.
Commutativity is unnecessary here: all ambient involutions have rank four. -/
theorem case_eleven_no_rankTwo (σ : F ≃+* F) (ρ : Representation (ZMod 2) H V)
    (e : generalizedFitting H ≃* PSL(2,F))
    (h : Nonempty ((extendScalars F ((ρ.comp (generalizedFitting H).subtype).comp
      (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm).symm.toMonoidHom)).Equiv
        (twistedTriple σ)))
    (X : Subgroup H) [IsElementaryAbelian 2 X] (g : H) (hg : g ∈ X) :
    Module.finrank (ZMod 2) (movedSpace ρ g) ≠ 2 := by
  by_cases h1 : g = 1
  · subst g
    have hz := finrank_movedSpace_one ρ
    omega
  · have ho : orderOf g = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian g hg) h1
    rw [case_eleven_rank_eq_four σ ρ e h g ho]
    decide

end Representation.RankTwo.TwistedTensor
