module
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.Cocycle
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.Descent.Application
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.AutomorphismDescription
/-!
# Outer involution descent in the actual binary G₂ model

Full inner-field coverage supplies the coefficient action of an arbitrary
outer involution. The proved root-coordinate cocycle theorem constructs an
inner conjugator, and coefficient restriction identifies its full fixed group
with G₂ over the actual fixed subfield. That field has exactly half the binary
degree. The two-residual is its derived group, retaining the proper G₂(2)′
endpoint while the full fixed group at that endpoint remains G₂(2).

All normal-form, cocycle-solving and coefficient-descent premises are proved.
Source: Aschbacher--Smith 16.1.4(4), printed p.1171; the full binary endpoint
on p.1191; and the fixed-component uses in E.6.18, E.6.23 and 2.5.19.
The octonion action and root formulas retain the imported ATLAS attribution.
-/
public section
namespace Atlas.G2.EvenFieldFixedResidual
open LieAutomorphismExtensions
variable {F : Type*} [Field F] [Finite F]
/-- An arbitrary outer involution has an actual inner-field normal form,
with the full fixed group over the coefficient fixed field and the correct
binary derived endpoint for the two-residual. -/
theorem outer_involution_conclusion {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card F = 2 ^ n) (a : MulAut (Model F)) (ha : orderOf a = 2)
    (hout : ∀ g : Model F, a ≠ MulAut.conj g) :
    ∃ (σ : F ≃+* F) (m : ℕ), 0 < m ∧ n = 2 * m ∧
      Nat.card (fixedField σ) = 2 ^ m ∧ orderOf σ = 2 ∧
      orderOf (fieldAction σ) = 2 ∧
      (∃ c : Model F, a = MulAut.conj c * fieldAction σ * (MulAut.conj c)⁻¹) ∧
      Nonempty (a.fixedSubgroup ≃* Model (fixedField σ)) ∧
      Nonempty (pResidual 2 a.fixedSubgroup ≃* commutator (Model (fixedField σ))) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (show Fintype.card F = 2 ^ n by simpa only [Nat.card_eq_fintype_card] using hc)
  have hq : 2 < Nat.card F := by
    rw [hc]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) (show 1 < n by omega)
  have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  obtain ⟨g, σ, he⟩ := exists_inner_field hq a
  obtain ⟨hs, hg⟩ := coefficient_involution_and_cocycle hq a ha2 g σ he hout
  obtain ⟨m, hm, hnm, hcard, hsact, hconj, hfixed, hres⟩ :=
    field_involution_conclusion_of_coboundary hn hc a ha2 g σ he hout
      (cocycle_eq_coboundary hq σ hs g hg)
  exact ⟨σ, m, hm, hnm, hcard, hs, hsact, hconj, hfixed, hres⟩

/-- The fixed field is strictly smaller, with its inherited coefficient
inclusion and exactly half the original binary degree. -/
theorem outer_involution_smaller_fixed_model {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card F = 2 ^ n) (a : MulAut (Model F)) (ha : orderOf a = 2)
    (hout : ∀ g : Model F, a ≠ MulAut.conj g) :
    ∃ (σ : F ≃+* F) (m : ℕ), 0 < m ∧ m < n ∧ n = 2 * m ∧
      Nat.card (fixedField σ) = 2 ^ m ∧
      Nonempty (a.fixedSubgroup ≃* Model (fixedField σ)) := by
  obtain ⟨σ,m,hm,hnm,hcard,_,_,_,he,_⟩ := outer_involution_conclusion hn hc a ha hout
  exact ⟨σ,m,hm,by omega,hnm,hcard,he⟩
end Atlas.G2.EvenFieldFixedResidual
