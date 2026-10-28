module
public import Theory.Mathieu.M12.Properties.AutCover
public import Theory.Mathieu.M12.Properties.SylowCentralizing
public import Theory.Mathieu.M12.TwoCentralInvolutions.CentralizerOrder
public import Theory.Mathieu.M22.Properties.SylowPointwise.Innerness
public import Theory.Mathieu.M22.Properties.FourNormalizers.Hexads
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Automorphisms
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoCentral
public import Theory.GroupAction.FourGroupSylowCentralizer

/-!
# Fixed cubic elements for Sylow-fixing Mathieu automorphisms

An inner involutory automorphism fixing a Sylow two-subgroup is induced by
an involution in that Sylow center. The concrete M₁₂ and M₂₄ two-central
centralizer orders are 192 and 21504; every M₂₂ involution centralizer has
order 384. Each is divisible by three, so Cauchy's theorem supplies a fixed
element of order three. The existing pointwise-Sylow innerness results
discharge the automorphism premise for all three native models.

Source: Aschbacher--Smith, the irreducible branch of 15.3.58, printed p.1149;
the marked centralizer calculations retain their references to GLS3,
Tables 5.3b, 5.3c and 5.3e, in their owning model modules.
-/

public section
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
namespace Sporadic.Mathieu

private theorem fixed_cubic_of_inner_twoCentral {D : Type*} [Group D] [Finite D]
    (hZ : center D = ⊥)
    (hcard : ∀ d : D, orderOf d = 2 → TwoCentral d →
      3 ∣ Nat.card (centralizer ({d} : Set D)))
    (a : MulAut D) (ha : orderOf a = 2) (S : Sylow 2 D)
    (hS : ∀ x ∈ S, a x = x) (hinner : ∃ d : D, a = MulAut.conj d) :
    ∃ c : D, orderOf c = 3 ∧ a c = c := by
  obtain ⟨d, rfl⟩ := hinner
  have hd : orderOf d = 2 :=
    (orderOf_injective MulAut.conj
      (MulAut.conj_injective_of_center_eq_bot hZ) d).symm.trans ha
  have hdc : d ∈ centralizer (S : Set D) := by
    intro x hx
    exact (mul_inv_eq_iff_eq_mul.mp (hS x hx)).symm
  have hdS : d ∈ S := Theory.GroupAction.mem_sylow_of_sq_eq_one_of_centralizes S
    (hd ▸ pow_orderOf_eq_one d) hdc
  have hcentral : TwoCentral d :=
    ⟨S, hdS, mem_center_iff.mpr (fun x => Subtype.ext (hdc x x.property))⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card'
    (G := centralizer ({d} : Set D)) 3 (hcard d hd hcentral)
  refine ⟨c, (Subgroup.orderOf_coe c).trans hc, ?_⟩
  change d * (c : D) * d⁻¹ = c
  exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp c.property).symm

/-- Every involutory automorphism fixing an M₁₂ Sylow two-subgroup fixes a cubic. -/
theorem m12_fixed_cubic_of_fixes_sylow (a : MulAut M12) (ha : orderOf a = 2)
    (S : Sylow 2 M12) (hS : ∀ x ∈ S, a x = x) :
    ∃ c : M12, orderOf c = 3 ∧ a c = c := by
  apply fixed_cubic_of_inner_twoCentral m12_center_eq_bot _ a ha S hS
    (m12_automorphism_inner_of_fixes_sylow a S hS)
  intro d hd hc
  rw [M12Involutions.card_centralizer_of_twoCentral d hd hc]
  norm_num

/-- Every involutory automorphism fixing an M₂₂ Sylow two-subgroup fixes a cubic. -/
theorem m22_fixed_cubic_of_fixes_sylow (a : MulAut M22) (ha : orderOf a = 2)
    (S : Sylow 2 M22) (hS : ∀ x ∈ S, a x = x) :
    ∃ c : M22, orderOf c = 3 ∧ a c = c := by
  apply fixed_cubic_of_inner_twoCentral m22_center_eq_bot _ a ha S hS
    (M22SylowPointwise.automorphism_inner_of_fixes_sylow a S hS)
  intro d hd _
  rw [M22FourNormalizers.involution_centralizer_card d hd]
  norm_num

/-- Every involutory automorphism fixing an M₂₄ Sylow two-subgroup fixes a cubic. -/
theorem m24_fixed_cubic_of_fixes_sylow (a : MulAut M24) (ha : orderOf a = 2)
    (S : Sylow 2 M24) (hS : ∀ x ∈ S, a x = x) :
    ∃ c : M24, orderOf c = 3 ∧ a c = c := by
  apply fixed_cubic_of_inner_twoCentral M24InvolutionCentralizers.center_eq_bot _
    a ha S hS
    (by obtain ⟨d, hd⟩ := M24OuterRestriction.conj_surjective a; exact ⟨d, hd.symm⟩)
  intro d hd hc
  rw [M24InvolutionCentralizers.card_centralizer_of_twoCentral d hd hc]
  norm_num

end Sporadic.Mathieu
