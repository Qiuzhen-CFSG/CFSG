module
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.Outer
public import Theory.GroupAction.AutomorphismFixedTransport
/-!
# Outer G₂ involutions on an isomorphic carrier

Transport preserves the original automorphism, innerness, and its literal
fixed subgroup. The full outer descent therefore gives an actual smaller
binary coefficient field, normal-form conjugator and derived residual also
on an arbitrary specified group carrier. No fixed-group equivalence is an
input. Source: Aschbacher--Smith 16.1.4(4), p.1171, and 2.5.19, p.562.
-/
public section
namespace Atlas.G2.EvenFieldFixedResidual
open LieAutomorphismExtensions
variable {F D : Type*} [Field F] [Finite F] [Group D]
/-- An actual model equivalence preserves the marked outer action, its fixed
subgroup and its two-residual during descent to the smaller binary field. -/
theorem outer_involution_conclusion_of_equiv (e : D ≃* Model F)
    {n : ℕ} (hn : 2 ≤ n) (hc : Nat.card F = 2 ^ n)
    (a : MulAut D) (ha : orderOf a = 2)
    (hout : ∀ g : D, a ≠ MulAut.conj g) :
    ∃ (σ : F ≃+* F) (m : ℕ), 0 < m ∧ m < n ∧ n = 2 * m ∧
      Nat.card (fixedField σ) = 2 ^ m ∧ orderOf σ = 2 ∧
      (∃ c : Model F, MulAut.congr e a =
        MulAut.conj c * fieldAction σ * (MulAut.conj c)⁻¹) ∧
      Nonempty (a.fixedSubgroup ≃* Model (fixedField σ)) ∧
      Nonempty (pResidual 2 a.fixedSubgroup ≃* commutator (Model (fixedField σ))) := by
  have hao : orderOf (MulAut.congr e a) = 2 := by
    simpa only [MulEquiv.orderOf_eq] using ha
  have hout' : ∀ g : Model F, MulAut.congr e a ≠ MulAut.conj g := by
    intro g hg
    obtain ⟨d, hd⟩ := (MulAut.congr_inner_iff e a).mp ⟨g, hg⟩
    exact hout d hd
  obtain ⟨σ,m,hm,hnm,hcard,hs,_,hc',⟨ef⟩,_⟩ :=
    outer_involution_conclusion hn hc (MulAut.congr e a) hao hout'
  let E := (MulAut.fixedSubgroupCongr e a).trans ef
  exact ⟨σ,m,hm,by omega,hnm,hcard,hs,hc',⟨E⟩,⟨residualEquivCommutator E⟩⟩
end Atlas.G2.EvenFieldFixedResidual
