module

public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.Cocycle
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.FieldDegree

/-!
# Conjugating an actual inner-field involution of G₂

The faithful semilinear action supplies the coefficient involution and cocycle
from the original outer involution. The cocycle theorem constructs a conjugator
in the split-octonion automorphism group, thereby removing the coboundary premise
of the field-involution fixed-group transport.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 16.1.4(4), printed p.1171, and the G₂(4) discussion on printed p.1191.
Coefficient fixed-group identification remains a separate result.
-/

public section

namespace Atlas.G2.EvenFieldFixedResidual
open LieAutomorphismExtensions
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- An outer involution with the supplied inner-field expression is conjugate,
by an actual octonion automorphism, to its coefficient automorphism. -/
theorem inner_field_involution_conjugate (hq : 2 < Nat.card F)
    (a : MulAut (Model F)) (ha : a ^ 2 = 1)
    (g : Model F) (σ : F ≃+* F)
    (he : a = MulAut.conj g * fieldAction σ)
    (hout : ∀ h : Model F, a ≠ MulAut.conj h) :
    ∃ c : Model F, a = MulAut.conj c * fieldAction σ * (MulAut.conj c)⁻¹ := by
  obtain ⟨hs, hg⟩ := coefficient_involution_and_cocycle hq a ha g σ he hout
  obtain ⟨c, hc⟩ := cocycle_eq_coboundary hq σ hs g hg
  refine ⟨c, ?_⟩
  rw [he, hc]
  apply MulEquiv.ext
  intro x
  change (c * fieldAction σ c⁻¹) * fieldAction σ x * (c * fieldAction σ c⁻¹)⁻¹ =
    c * fieldAction σ (c⁻¹ * x * c) * c⁻¹
  simp only [map_mul, map_inv]
  group

end Atlas.G2.EvenFieldFixedResidual
