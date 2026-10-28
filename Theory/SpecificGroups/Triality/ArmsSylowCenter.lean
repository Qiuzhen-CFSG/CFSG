module
public import Theory.GroupTheory.PCoreSylowCenter
public import Theory.SpecificGroups.Triality.ArmsLocalCoreCenter
public import Theory.SpecificGroups.Triality.ArmsParabolicAtTwo
public import Theory.SpecificGroups.Triality.SylowParabolicExtensions

/-!
# Sylow centers in the binary-triality arms parabolic

The root radical is self-centralizing, its center is central in the arms
factor, and that center has order two at q=2. Transport through the actual
parabolic isomorphism identifies the center of each chosen Sylow subgroup.

Source: Aschbacher–Smith F.1.12(I)(4) and 5.2.2, pp.263–264,647–648;
the underlying root calculations are in the imported triality modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Triality.Standard.Parabolics
variable {X : Type*} [Group X]

/-- Every Sylow center in an actual binary arms parabolic has order two
and is central in that parabolic, with its original inclusion. -/
theorem binary_arms_sylow_center (e : X ≃* parabolic (binaryParameters 1 Nat.zero_lt_one) .arms)
    (S : Sylow 2 X) : Nat.card (center S) = 2 ∧
      (center S).map (S : Subgroup X).subtype ≤ center X := by
  let P := binaryParameters 1 Nat.zero_lt_one
  let a : X ≃* localFactor P .arms := e.trans
    (MulEquiv.subgroupCongr (parabolic_arms_eq_localFactor_at_two P rfl rfl))
  let b : pCore 2 X ≃* pCore 2 (localFactor P .arms) :=
    ((pCore 2 X).equivMapOfInjective a.toMonoidHom a.injective).trans
      (MulEquiv.subgroupCongr (pCore_map_iso 2 a))
  have hc : centralizer (pCore 2 X : Set X) ≤ pCore 2 X :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr
      (parabolic_centralizer_twoCore_le P rfl .arms)
  have hz : (center (pCore 2 X)).map (pCore 2 X).subtype ≤ center X := by
    rintro x ⟨q,hq,rfl⟩
    have hb : b q ∈ center (pCore 2 (localFactor P .arms)) := (centerCongr b ⟨q,hq⟩).property
    have hh := arms_core_center_le_center P rfl (mem_map_of_mem _ hb)
    apply mem_center_iff.mpr
    intro y
    apply a.injective
    have hbval : (b q : localFactor P .arms) = a q := by
      change ((pCore 2 X).equivMapOfInjective a.toMonoidHom a.injective q :
        localFactor P .arms) = a q
      exact coe_equivMapOfInjective_apply _ _ _ _
    have hcomm := mem_center_iff.mp hh (a y)
    change a y * (b q : localFactor P .arms) = (b q : localFactor P .arms) * a y at hcomm
    rw [hbval] at hcomm
    simpa only [map_mul, Subgroup.subtype_apply] using hcomm
  have he := mapped_sylow_center_eq_core_center S hc hz
  refine ⟨?_,he.trans_le hz⟩
  have hcard := congrArg (fun U : Subgroup X => Nat.card U) he
  rw [card_map_of_injective (S : Subgroup X).subtype_injective,
    card_map_of_injective (pCore 2 X).subtype_injective] at hcard
  exact hcard.trans ((Nat.card_congr (centerCongr b).toEquiv).trans
    (localFactor_arms_twoCore_center_card P rfl))
end Triality.Standard.Parabolics
