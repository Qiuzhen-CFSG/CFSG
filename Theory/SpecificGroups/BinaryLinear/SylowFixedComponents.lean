module

public import Theory.SpecificGroups.BinaryLinear.SylowPointwiseInner
public import Theory.SpecificGroups.BinaryLinear.RootCentralizerParabolic
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.Quasithin.EvenCharacteristic
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion

/-!
# No components in pointwise Sylow fixers of binary linear groups

In dimensions four and five a nonidentity automorphism fixing a Sylow
two-subgroup pointwise is conjugation by a transvection. Its centralizer lies
in a proper parabolic and contains the given Sylow subgroup. It therefore
inherits the parabolic's self-centralizing two-core, which excludes components.

Source: Aschbacher–Smith, E.6.22, printed p.254, and 16.1.6, p.1172.
-/

public section
namespace BinaryLinear.OuterCyclic
open Subgroup Theory.GroupTheory

/-- The actual fixed subgroup of a nonidentity pointwise Sylow fixer has
self-centralizing two-core, including both binary dimensions four and five. -/
theorem sylow_fixed_twoCore {n : ℕ} (hn : n = 4 ∨ n = 5)
    (S : Sylow 2 (LinearGroup n)) (a : MulAut (LinearGroup n)) (ha : a ≠ 1)
    (hfix : ∀ x ∈ (S : Subgroup (LinearGroup n)), a x = x) :
    centralizer (pCore 2 a.fixedSubgroup : Set a.fixedSubgroup) ≤
      pCore 2 a.fixedSubgroup := by
  obtain ⟨z, _, hz, ht⟩ := sylow_fixing_ne_one_transvection hn S a hfix ha
  obtain ⟨W, hW, hWt, _, hC⟩ := RootCentralizer.transvection_proper_parabolic ht
  rw [← hz] at hC
  have hS : (S : Subgroup (LinearGroup n)) ≤ a.fixedSubgroup := by
    intro x hx
    exact (MulAut.mem_fixedSubgroup a x).mpr (hfix x hx)
  have hrel := centralizer_pCore_le_of_sylow_le (S.subtype (hS.trans hC))
    (a.fixedSubgroup.subgroupOf (parabolic W)) (fun x hx => hS hx)
    (centralizer_parabolic_twoCore_le hW hWt)
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hC)).mp hrel

/-- Ordinary components cannot occur in these fixed subgroups. -/
theorem sylow_fixed_no_component {n : ℕ} (hn : n = 4 ∨ n = 5)
    (S : Sylow 2 (LinearGroup n)) (a : MulAut (LinearGroup n)) (ha : a ≠ 1)
    (hfix : ∀ x ∈ (S : Subgroup (LinearGroup n)), a x = x)
    (D : Subgroup a.fixedSubgroup) : ¬ IsComponent a.fixedSubgroup D := by
  let : Finite (LinearGroup n) :=
    Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective
  exact not_isComponent_of_twoCore (sylow_fixed_twoCore hn S a ha hfix) D

end BinaryLinear.OuterCyclic
