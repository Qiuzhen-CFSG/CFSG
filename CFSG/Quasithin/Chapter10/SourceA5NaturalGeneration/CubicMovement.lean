module
public import Theory.GroupTheory.PResidual.SimpleQuotientCommutator
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2OddFixed
public import Theory.SpecificGroups.Alternating.FiveComponents
/-!
# The source cubic torus moves the entire natural component

A cubic subgroup has nonzero image in the original alternating-five
quotient, since its kernel is a two-group. Simplicity makes that image move
the entire quotient; two-perfection lifts the commutator identity to the
original component. No splitting of its two-core is required.

This discharges K=[K,D₁] in the common-component step of
Aschbacher–Smith 10.2.3(4), printed p.747.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open ChapterC
variable {G : Type*} [Group G] [Finite G]
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

omit [Finite G] in
/-- A literal cubic subgroup moves the whole two-perfect A₅ core cover. -/
theorem source_a5_cubic_component_moved (K D : Subgroup G) (hK : IsPPerfect 2 K)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (hDK : D ≤ K) (hD : Nat.card D = 3) : ⁅K,D⁆ = K := by
  let R := D.subgroupOf K
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hR : Nat.card R = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hDK).toEquiv).trans hD
  have hn : ¬ R ≤ q.ker := by
    intro he
    have hp : IsPGroup 2 R := (hk ▸ (pCore_isPGroup (p := 2) (G := K))).to_le he
    rcases hp.card_eq_or_dvd with hc | hc <;> rw [hR] at hc <;> norm_num at hc
  have hs := commutator_top_eq_of_pPerfect_simple_quotient hK q hq
    (hk ▸ (pCore_isPGroup (p := 2) (G := K)))
    (alternatingGroup.center_eq_bot (by simp)) R hn
  have hm := congrArg (map K.subtype) hs
  simpa only [map_commutator,R,map_subgroupOf_eq_of_le hDK,
    ←MonoidHom.range_eq_map,range_subtype] using hm

omit [Finite G] in
/-- The intrinsic natural block supplies the original alternating-five quotient. -/
theorem source_natural_cubic_component_moved (K D : Subgroup G) (hK : IsL2EvenBlock K 2)
    (hDK : D ≤ K) (hD : Nat.card D = 3) : ⁅K,D⁆ = K := by
  obtain ⟨e⟩ := hK.four_quotient_alternatingFive
  exact source_a5_cubic_component_moved K D hK.2.1.twoPerfect e hDK hD
end CFSG.Quasithin.Chapter10
