module

public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.FieldDegree
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.Residual
public import Theory.GroupAction.AutomorphismFixedResidualTransport

/-!
# G₂ field involutions: parameters, residuals, and descent transport

The parameter reduction proves that an outer involution given as inner times
field has an involutory coefficient component and satisfies the cocycle
equation. Its coefficient fixed field has half the binary degree. The residual
calculation identifies O²(G₂(k)) with its actual derived subgroup for every
finite field k, retaining the proper G₂(2)′ endpoint.

The transport below assembles the desired fixed groups from two explicit
inputs: a coboundary solving the cocycle, and an actual equivalence for the
pure coefficient fixed group. Construction of those two inputs is still
required to complete the field-involution theorem. No global automorphism
coverage or central-cover lifting is asserted here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 16.1.4(4), printed p.1171, and the G₂(4) fixed-group discussion on
printed p.1191.
-/

public section

namespace Atlas.G2.EvenFieldFixedResidual
open LieAutomorphismExtensions
variable {F : Type*} [Field F]

/-- A specified coboundary gives actual conjugacy in the automorphism group. -/
theorem conjugate_eq_of_coboundary (a : MulAut (Model F))
    (g c : Model F) (σ : F ≃+* F)
    (he : a = MulAut.conj g * fieldAction σ)
    (hg : g = c * fieldAction σ c⁻¹) :
    a = MulAut.conj c * fieldAction σ * (MulAut.conj c)⁻¹ := by
  rw [he, hg]
  apply MulEquiv.ext
  intro x
  change (c * fieldAction σ c⁻¹) * fieldAction σ x * (c * fieldAction σ c⁻¹)⁻¹ =
    c * fieldAction σ (c⁻¹ * x * c) * c⁻¹
  simp only [map_mul, map_inv]
  group

/-- Conjugation by the inverse coboundary restricts to the genuine fixed
subgroups. The coboundary is still an explicit input. -/
noncomputable def fixedEquivOfCoboundary (a : MulAut (Model F))
    (g c : Model F) (σ : F ≃+* F)
    (he : a = MulAut.conj g * fieldAction σ)
    (hg : g = c * fieldAction σ c⁻¹) :
    a.fixedSubgroup ≃* (fieldAction σ).fixedSubgroup := by
  apply MulAut.fixedSubgroupEquivOfCompatible (MulAut.conj c⁻¹) a (fieldAction σ)
  intro x
  change c⁻¹ * a x * c = fieldAction σ (c⁻¹ * x * c)
  rw [he]
  change c⁻¹ * (g * fieldAction σ x * g⁻¹) * c = fieldAction σ (c⁻¹ * x * c)
  rw [hg]
  simp only [map_mul, map_inv]
  group

/-- Conditional final transport. The cocycle-solving witness and coefficient
descent equivalence must both be constructed before this gives the source
field-involution conclusion. -/
theorem field_involution_conclusion_of_coboundary_of_descent [Finite F]
    {n : ℕ} (hn : 2 ≤ n) (hc : Nat.card F = 2 ^ n)
    (a : MulAut (Model F)) (ha : a ^ 2 = 1)
    (g : Model F) (σ : F ≃+* F)
    (he : a = MulAut.conj g * fieldAction σ)
    (hout : ∀ h : Model F, a ≠ MulAut.conj h)
    (hboundary : ∃ c : Model F, g = c * fieldAction σ c⁻¹)
    (descent : (fieldAction σ).fixedSubgroup ≃* Model (fixedField σ)) :
    ∃ m : ℕ, 0 < m ∧ n = 2 * m ∧ Nat.card (fixedField σ) = 2 ^ m ∧
      orderOf (fieldAction σ) = 2 ∧
      (∃ c : Model F, a = MulAut.conj c * fieldAction σ * (MulAut.conj c)⁻¹) ∧
      Nonempty (a.fixedSubgroup ≃* Model (fixedField σ)) ∧
      Nonempty (pResidual 2 a.fixedSubgroup ≃* commutator (Model (fixedField σ))) := by
  obtain ⟨hs, _, m, hm, hn', hcard⟩ := field_involution_parameters hn hc a ha g σ he hout
  obtain ⟨c, hc'⟩ := hboundary
  let e := (fixedEquivOfCoboundary a g c σ he hc').trans descent
  refine ⟨m, hm, hn', hcard, ?_, ⟨c, conjugate_eq_of_coboundary a g c σ he hc'⟩,
    ⟨e⟩, ⟨residualEquivCommutator e⟩⟩
  rw [orderOf_injective fieldAction fieldAction_injective, hs]

end Atlas.G2.EvenFieldFixedResidual
