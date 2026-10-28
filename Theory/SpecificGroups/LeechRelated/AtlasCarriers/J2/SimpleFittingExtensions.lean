module

public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Automorphisms.Full
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Sylow

/-!
# Finite groups with a simple Hall--Janko generalized Fitting subgroup

Conjugation on the genuine generalized Fitting subgroup, followed by its
specified J₂ equivalence, embeds the ambient group in the full automorphism
group. The checked automorphism equivalence realizes this as the explicit
permutation extension and sends every socle element to its literal carrier
inclusion. The range therefore contains the inner carrier. Its certified
index is two, so there are exactly two possibilities for the ambient range.

The degree-100 carrier is nonabelian because its permutation centralizer is
trivial and its specified central involution is nonidentity. Simplicity is
inherited from the source's generalized Fitting subgroup; no independent
simplicity certification of the model is needed. The result applies to all
finite ambient groups with this simple generalized Fitting subgroup.

Source: the generalized Fitting centralizer theorem and the checked ATLAS
J2G1-p100B0 automorphism calculations. Application: Aschbacher--Smith
E.1.14(5), printed p.214, including its outer two-extensions.
-/

public section
namespace Sporadic.LeechRelated.J2.SimpleFittingExtensions

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Sporadic.LeechRelated.J2
open Sporadic.LeechRelated.J2.ExceptionalParabolics

private theorem carrier_not_commutative : ¬ IsMulCommutative Carrier := by
  intro h
  let := h
  have hz : inclusion Seed.z ∈ centralizer (generated : Set (Equiv.Perm (Fin 100))) := by
    intro x hx
    exact congrArg inclusion (mul_comm (⟨x, hx⟩ : Carrier) Seed.z)
  rw [permutation_centralizer_eq_bot, mem_bot] at hz
  exact Seed.z_ne_one (inclusion_injective (by simpa only [map_one] using hz))

private theorem inner_index : intoExtension.range.index = 2 := by
  have hc : Nat.card intoExtension.range = 604800 :=
    (Nat.card_congr (MonoidHom.ofInjective SecondParabolic.intoExtension_injective).toEquiv).symm.trans
      (SecondParabolic.card_carrier FirstParabolic.card_l₁)
  have h := intoExtension.range.card_mul_index
  rw [hc, SecondParabolic.card_extension FirstParabolic.card_l₁] at h
  omega

private theorem overgroup_cases (H : Subgroup Extension) (hH : intoExtension.range ≤ H) :
    H = intoExtension.range ∨ H = ⊤ := by
  have hd : H.index ∣ 2 := inner_index ▸ Subgroup.index_dvd_of_le hH
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact Or.inr (Subgroup.index_eq_one.mp h)
  · have hm := Subgroup.relIndex_mul_index hH
    rw [h, inner_index] at hm
    have hr : intoExtension.range.relIndex H = 1 := by omega
    exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp hr) hH)

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem fitting_not_commutative (e : generalizedFitting G ≃* Carrier) :
    ¬ IsMulCommutative (generalizedFitting G) := by
  intro h
  let := h
  apply carrier_not_commutative
  exact IsMulCommutative.of_comm fun x y => e.symm.injective (by
    simp only [map_mul, mul_comm])

noncomputable def ambientAction (e : generalizedFitting G ≃* Carrier) : G →* Extension :=
  extensionEquivAut.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := generalizedFitting G)))

theorem ambientAction_injective [IsSimpleGroup (generalizedFitting G)]
    (e : generalizedFitting G ≃* Carrier) : Function.Injective (ambientAction e) :=
  extensionEquivAut.symm.injective.comp ((MulAut.congr e).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot _
      (SimpleSocle.centralizer_eq_bot (fitting_not_commutative e))))

theorem ambientAction_on_fitting (e : generalizedFitting G ≃* Carrier)
    (x : generalizedFitting G) : ambientAction e x = intoExtension (e x) := by
  apply extensionEquivAut.injective
  change extensionEquivAut (extensionEquivAut.symm _) = _
  rw [extensionEquivAut.apply_symm_apply, extensionEquivAut_intoExtension]
  change MulAut.congr e (MulAut.conjNormal (x : G)) = MulAut.conj (e x)
  rw [MulAut.conjNormal_val, MulAut.congr_conj]

theorem inner_le_ambientAction_range (e : generalizedFitting G ≃* Carrier) :
    intoExtension.range ≤ (ambientAction e).range := by
  rintro a ⟨x, rfl⟩
  refine ⟨e.symm x, ?_⟩
  rw [ambientAction_on_fitting, e.apply_symm_apply]

theorem ambient_equiv_cases [IsSimpleGroup (generalizedFitting G)]
    (e : generalizedFitting G ≃* Carrier) :
    Nonempty (G ≃* Carrier) ∨ Nonempty (G ≃* Extension) := by
  let d := MonoidHom.ofInjective (ambientAction_injective e)
  rcases overgroup_cases (ambientAction e).range (inner_le_ambientAction_range e) with h | h
  · exact Or.inl ⟨(d.trans (MulEquiv.subgroupCongr h)).trans
      (MonoidHom.ofInjective SecondParabolic.intoExtension_injective).symm⟩
  · exact Or.inr ⟨(d.trans (MulEquiv.subgroupCongr h)).trans Subgroup.topEquiv⟩

end Sporadic.LeechRelated.J2.SimpleFittingExtensions
