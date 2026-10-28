module

public import Theory.GroupTheory.NoncentralChiefRefinement.Transport
public import Theory.GroupTheory.CentralPChiefFactorsQuotient

/-!
# Central binary chief factors above a quotient kernel

Normal-subgroup correspondence takes chief intervals above the kernel to
chief intervals of the quotient. The literal relative-quotient isomorphism
intertwines conjugation, so centrality pulls back. Every such terminal
chief refinement therefore has zero noncentral binary contribution.
Source application: Aschbacher–Smith, 14.7.71(1), printed p.1075.
-/

public section

open Subgroup
namespace NoncentralChiefRefinement
variable {K : Type*} [Group K]

/-- Central binary chief factors of a quotient pull back above its kernel. -/
theorem isCentral_of_quotient_hasCentralTwoChiefFactors (Q : NormalNode K)
    (h : HasCentralPChiefFactors 2 (K ⧸ Q.val))
    {A B : NormalNode K} (hAB : A ⋖ B) (hQA : Q ≤ A)
    (hp : IsPGroup 2 (Section A B)) : IsCentral A B := by
  have hc := (covBy_iff_isChief _ _).mp
    ((quotientImage_covBy_iff Q A B hQA (hQA.trans hAB.le)).mpr hAB)
  have hz : IsCentral (quotientImage Q A) (quotientImage Q B) :=
    h _ _ inferInstance inferInstance hc.lt hc.minimal
      (hp.of_equiv (quotientSectionEquiv Q A B hQA))
  rw [isCentral_iff_action] at hz ⊢
  intro k x
  apply (quotientSectionEquiv Q A B hQA).injective
  rw [quotientSectionEquiv_equivariant, hz]

/-- The terminal refinement counts only noncentral factors, allowing central C₂ factors. -/
theorem ChiefSeries.noncentralTwoCount_eq_zero_of_centralTwo_quotient
    (s : ChiefSeries K) (Q : NormalNode K) (hQ : Q ≤ s.head)
    (h : HasCentralPChiefFactors 2 (K ⧸ Q.val)) : s.noncentralTwoCount = 0 := by
  apply Nat.card_eq_zero.mpr
  left
  refine ⟨fun i => ?_⟩
  exact i.property.2 (isCentral_of_quotient_hasCentralTwoChiefFactors Q h
    (s.step i.val) (hQ.trans (CompositionSeries.head_le i.val.castSucc)) i.property.1)

end NoncentralChiefRefinement
