module
public import Theory.GroupTheory.PResidual.NormalizedSupplement
public import Theory.GroupTheory.ConjugateSpanOrder
/-!
# Odd conjugate spans and removal of a normalizing prime-group error

The span of conjugates of a subgroup of order prime to p is p-perfect:
each seed element lies in the span's p-residual, which is characteristic.
If a p-perfect subgroup X has [L,X] contained in a p-group Q normalizing X,
then L normalizes X. Each conjugate of X lies in XQ, and its p-perfectness
removes the p-group supplement. Ambient normality of Q is unnecessary.

Source application: Aschbacher--Smith, the final odd-actor comparison in
4.4.3, printed p.623. The consumer uses the original X = ⟨A^T⟩.
-/
public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

/-- A coprime-order seed generates a p-perfect conjugate span. -/
theorem isPPerfect_conjugateSpanBy_of_coprime {p : ℕ}
    (A T : Subgroup G) (ho : Nat.Coprime p (Nat.card A)) :
    IsPPerfect p (conjugateSpanBy A T) := by
  let X := conjugateSpanBy A T
  let R := (pResidual p X).map X.subtype
  have hXR : normalizer (X : Set G) ≤ normalizer (R : Set G) :=
    normalizer_le_normalizer_characteristic_image X (pResidual p X)
  have hAR : A ≤ R := by
    intro a ha
    refine ⟨⟨a,le_conjugateSpanBy A T ha⟩,?_,rfl⟩
    apply mem_pResidual_of_orderOf_coprime
    rw [Subgroup.orderOf_mk]
    exact ho.of_dvd_right (A.orderOf_dvd_natCard ha)
  have hXR' : X ≤ R := conjugateSpanBy_le hAR
    ((le_normalizer_conjugateSpanBy A T).trans hXR)
  apply (pResidual_eq_top_iff p X).mp
  apply top_unique
  intro x _
  obtain ⟨y,hy,he⟩ := hXR' x.property
  exact (Subtype.ext he : y = x) ▸ hy

/-- A normalizing prime-group error can be removed from the action on a
prime-perfect subgroup. Both normalization conditions are relative. -/
theorem le_normalizer_of_isPPerfect_of_commutator_le {p : ℕ} [Fact p.Prime]
    (X L Q : Subgroup G) (hp : IsPPerfect p X) (hQ : IsPGroup p Q)
    (hQX : Q ≤ normalizer (X : Set G)) (hc : ⁅L,X⁆ ≤ Q) :
    L ≤ normalizer (X : Set G) := by
  apply le_normalizer_iff.mpr
  intro l hl x hx
  let e := MulAut.conj l
  have hle : X.map e.toMonoidHom ≤ X ⊔ Q := by
    rintro _ ⟨y,hy,rfl⟩
    have hh := (X ⊔ Q).mul_mem
      ((show Q ≤ X ⊔ Q from le_sup_right)
        (hc (commutator_mem_commutator hl hy)))
      ((show X ≤ X ⊔ Q from le_sup_left) hy)
    change l * y * l⁻¹ ∈ X ⊔ Q
    simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one,
      MulAut.conj_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] using hh
  have hp' := hp.of_surjective (X.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom
    (X.equivMapOfInjective e.toMonoidHom e.injective).surjective
  exact le_of_isPPerfect_of_le_sup_of_normalizes (X.map e.toMonoidHom) X Q
    hp' hQ hQX hle (mem_map_of_mem e.toMonoidHom hx)
end Subgroup
