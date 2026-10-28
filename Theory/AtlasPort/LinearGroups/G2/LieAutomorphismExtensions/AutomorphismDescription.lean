module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage

/-!
# The full inner-field automorphism description

For a finite field F of characteristic two with more than two elements,
conjugation and coefficientwise octonion transport give an isomorphism
G₂(F) ⋊ Aut(F) ≃ Aut(G₂(F)). Injectivity is the center and trace calculation;
surjectivity is the concrete root-frame alignment and parameter rigidity.
The inverse isomorphism defines a canonical field-component homomorphism,
whose kernel consists exactly of the inner automorphisms.

Source: the automorphism input on printed p.264 in Aschbacher--Smith F.1.12.
This supplies the global description used with the local PSL₂ quotient
actions; it does not assume a prescribed action on the roots.
-/

@[expose] public section

namespace Atlas.G2.LieAutomorphismExtensions
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The inner and genuine coefficientwise field actions identify the full automorphism group. -/
theorem semilinearAction_bijective (hq : 2 < Nat.card F) :
    Function.Bijective (semilinearAction (F := F)) :=
  ⟨semilinearAction_injective hq, semilinearAction_surjective hq⟩

/-- The actual semidirect-product description of Aut(G₂(F)) in even characteristic, q > 2. -/
noncomputable def semilinearEquiv (hq : 2 < Nat.card F) :
    Model F ⋊[fieldAction] (F ≃+* F) ≃* MulAut (Model F) :=
  MulEquiv.ofBijective semilinearAction (semilinearAction_bijective hq)

@[simp] theorem semilinearEquiv_apply (hq : 2 < Nat.card F)
    (z : Model F ⋊[fieldAction] (F ≃+* F)) :
    semilinearEquiv hq z = MulAut.conj z.left * fieldAction z.right := rfl

/-- The field component of an abstract automorphism, obtained from the proved decomposition. -/
noncomputable def fieldComponent (hq : 2 < Nat.card F) :
    MulAut (Model F) →* (F ≃+* F) :=
  SemidirectProduct.rightHom.comp (semilinearEquiv hq).symm.toMonoidHom

@[simp] theorem fieldComponent_inner_field (hq : 2 < Nat.card F)
    (g : Model F) (σ : F ≃+* F) :
    fieldComponent hq (MulAut.conj g * fieldAction σ) = σ := by
  change ((semilinearEquiv hq).symm (semilinearEquiv hq ⟨g, σ⟩)).right = σ
  rw [MulEquiv.symm_apply_apply]

/-- An automorphism has trivial field component exactly when it is inner. -/
theorem fieldComponent_eq_one_iff (hq : 2 < Nat.card F) (a : MulAut (Model F)) :
    fieldComponent hq a = 1 ↔ ∃ g : Model F, a = MulAut.conj g := by
  obtain ⟨g, σ, rfl⟩ := exists_inner_field hq a
  rw [fieldComponent_inner_field]
  constructor
  · rintro rfl
    exact ⟨g, by rw [map_one, mul_one]⟩
  · rintro ⟨h, hh⟩
    apply fieldAction_eq_conj_implies_one σ (g⁻¹ * h)
    rw [map_mul, map_inv]
    exact (eq_inv_mul_iff_mul_eq).mpr hh

end Atlas.G2.LieAutomorphismExtensions
