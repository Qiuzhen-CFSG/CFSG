module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.PerfectLifting.CubicModels
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.ProductComponents.FactorModels
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.QuasisimpleModels

/-!
# Cubic witnesses on the source component presentations

The concrete cubic witnesses transport through the actual equivalences in
B.5.6's group catalogue. The triple-six presentation only identifies the
center and central quotient, so it needs a separate argument: lift a
three-cycle and an inverting even involution from A₆. A suitable commutator
has nontrivial cubic image and is inverted by the lifted involution.
Its cube is central, hence is both inverted and fixed; the cubic center
then forces that cube to be one. No identification of an arbitrary central
cover with the concrete hexacode model is assumed.

The product models use the proved perfect-factor witnesses or the explicit
three-cycle in the A₅ component of S₅. The actual consumers are the
component constructions in `ClassifiedComponents`.
Source: Aschbacher–Smith, B.5.1 and B.5.6, printed pp.99–105, and
15.3.49(i), pp.1143–1144 (combined manuscript, 1 March 2004).
-/

public section
open Subgroup Equiv Theory.GroupTheory Theory.SpecificGroups.NoncentralCubic
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

private theorem triple_cubic {D : Type*} [Group D]
    (ez : center D ≃* Multiplicative (ZMod 3))
    (eq : (D ⧸ center D) ≃* alternatingGroup (Fin 6)) :
    ∃ x : D, orderOf x = 3 ∧ x ∉ center D := by
  let f := eq.toMonoidHom.comp (QuotientGroup.mk' (center D))
  have hf : Function.Surjective f := eq.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker (x : D) : f x = 1 ↔ x ∈ center D := by
    change eq (QuotientGroup.mk' (center D) x) = 1 ↔ _
    rw [eq.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hcube (x : D) (hx : x ∈ center D) : x ^ 3 = 1 := by
    have h : (⟨x, hx⟩ : center D) ^ 3 = 1 := by
      apply ez.injective
      rw [map_pow, map_one]
      exact (by decide : ∀ a : Multiplicative (ZMod 3), a ^ 3 = 1) _
    exact congrArg Subtype.val h
  let a : alternatingGroup (Fin 6) := ⟨swap 0 1 * swap 1 2, by
    simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]⟩
  let b : alternatingGroup (Fin 6) := ⟨swap 0 1 * swap 3 4, by
    simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]⟩
  have hb : b ^ 2 = 1 := by decide
  obtain ⟨x, hx⟩ := hf a
  obtain ⟨y, hy⟩ := hf b
  have hyc : y ^ 2 ∈ center D := (hker _).mp (by rw [map_pow, hy, hb])
  let t := y ^ 3
  have ht : t ^ 2 = 1 := by
    change (y ^ 3) ^ 2 = 1
    rw [← pow_mul, show 3 * 2 = 2 * 3 by decide, pow_mul]
    exact hcube _ hyc
  have hft : f t = b := by
    change f (y ^ 3) = b
    rw [map_pow, hy]
    decide
  let c := ⁅x, t⁆
  have hfc : f c = ⁅a, b⁆ := by
    change f ⁅x, t⁆ = _
    rw [map_commutatorElement, hx, hft]
  have hc3 : c ^ 3 ∈ center D := (hker _).mp (by
    rw [map_pow, hfc]
    decide +kernel)
  have hinv : t * c * t⁻¹ = c⁻¹ := by
    have hti : t⁻¹ = t := by
      apply inv_eq_of_mul_eq_one_left
      simpa only [pow_two] using ht
    dsimp [c]
    simp only [commutatorElement_def, mul_inv_rev, inv_inv]
    simp only [hti, mul_assoc, ← pow_two, ht, mul_one]
  have hpow : (c ^ 3) ^ 2 = 1 := by
    have hcomm := mem_center_iff.mp hc3 t
    have he : c ^ 3 = (c ^ 3)⁻¹ := by
      calc
        c ^ 3 = t * c ^ 3 * t⁻¹ := by rw [hcomm, mul_inv_cancel_right]
        _ = (t * c * t⁻¹) ^ 3 := conj_pow.symm
        _ = (c ^ 3)⁻¹ := by rw [hinv, inv_pow]
    calc
      (c ^ 3) ^ 2 = (c ^ 3) * (c ^ 3) := pow_two _
      _ = (c ^ 3)⁻¹ * (c ^ 3) := congrArg (fun z => z * c ^ 3) he
      _ = 1 := inv_mul_cancel _
  have hc : c ^ 3 = 1 := by
    have hdiv := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpow)
      (orderOf_dvd_of_pow_eq_one (hcube _ hc3))
    have ho : orderOf (c ^ 3) = 1 := Nat.eq_one_of_dvd_one hdiv
    exact orderOf_eq_one_iff.mp ho
  have hn : c ∉ center D := by
    intro hh
    have he := (hker c).mpr hh
    rw [hfc] at he
    exact (by decide : ⁅a, b⁆ ≠ 1) he
  exact ⟨c, orderOf_eq_prime hc (fun h => hn (h ▸ (center D).one_mem)), hn⟩

/-- Every source generalized-Fitting model supplies a noncentral cubic,
including the central-cover presentation and the small field endpoints. -/
theorem noncentral_cubic_of_quasisimpleModel {D : Type*} [Group D]
    (h : QuasisimpleModel D) : ∃ x : D, orderOf x = 3 ∧ x ∉ center D := by
  cases h with
  | linearTwo F e =>
    exact exists_noncentral_orderOf_of_injective e.symm.toMonoidHom e.symm.injective
      (exists_noncentral_cubic_specialLinear F.Carrier (by decide : 2 ≤ 2))
  | linearThree F e =>
    exact exists_noncentral_orderOf_of_injective e.symm.toMonoidHom e.symm.injective
      (exists_noncentral_cubic_specialLinear F.Carrier (by decide : 2 ≤ 3))
  | symplecticFour F e =>
    exact exists_noncentral_orderOf_of_injective e.symm.toMonoidHom e.symm.injective
      (exists_noncentral_cubic_symplecticFour F.Carrier)
  | g2 F e =>
    exact exists_noncentral_orderOf_of_injective e.symm.toMonoidHom e.symm.injective
      (exists_noncentral_cubic_g2 F.Carrier)
  | alternatingSix e =>
    exact exists_noncentral_orderOf_of_injective e.symm.toMonoidHom e.symm.injective
      (exists_noncentral_cubic_alternating 6 (Or.inl rfl))
  | alternatingSeven e =>
    exact exists_noncentral_orderOf_of_injective e.symm.toMonoidHom e.symm.injective
      (exists_noncentral_cubic_alternating 7 (Or.inr rfl))
  | tripleSix ez eq => exact triple_cubic ez eq
  | g2DerivedTwo e =>
    exact exists_noncentral_orderOf_of_injective e.symm.toMonoidHom e.symm.injective
      exists_noncentral_cubic_g2Derived
  | linearFourTwo e =>
    exact exists_noncentral_orderOf_of_injective e.symm.toMonoidHom e.symm.injective
      (exists_noncentral_cubic_specialLinear (ZMod 2) (by decide : 2 ≤ 4))
  | linearFiveTwo e =>
    exact exists_noncentral_orderOf_of_injective e.symm.toMonoidHom e.symm.injective
      (exists_noncentral_cubic_specialLinear (ZMod 2) (by decide : 2 ≤ 5))

/-- The perfect product factors and the A₅ component of S₅ all have the
cubic witness required for outside placement. -/
theorem noncentral_cubic_of_componentModel {D : Type*} [Group D]
    (h : ProductComponents.ComponentModel D) :
    ∃ x : D, orderOf x = 3 ∧ x ∉ center D := by
  rcases h with h | h
  · exact h.exists_noncentral_cubic
  · obtain ⟨e⟩ := h
    exact exists_noncentral_orderOf_of_injective e.symm.toMonoidHom e.symm.injective
      ⟨ProductComponents.a5ThreeCycle, ProductComponents.a5ThreeCycle_order,
        ProductComponents.a5ThreeCycle_noncentral⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence
