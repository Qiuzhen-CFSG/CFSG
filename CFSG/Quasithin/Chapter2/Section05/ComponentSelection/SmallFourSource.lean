module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallFourFacts
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ComponentSylowMark

/-!
# Four-group assertions on the original normal-component source action

The homomorphism is conjugation by H on its actual normal component L,
using L.normalizerMonoidHom and the original inclusion. Inner automorphisms
from F ≤ S ∩ L come from those same elements of S. The full model theorem
therefore gives the literal Aut_S(L) containment. If the original component
centralizer lies in S, its kernel removes the remaining action ambiguity
and yields C_H(F) ≤ S.

Source: Aschbacher--Smith 2.5.8(5) and its use in 2.5.12, pp.556,558.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup ComponentRefinement Stellmacher
variable {G : Type*} [Group G] [Finite G]
  {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The actual action of the source H on its normal component L. -/
def MathieuSourceSetup.componentAction (c : MathieuSourceSetup H L M S z)
    [(L.subgroupOf H).Normal] : H →* MulAut L :=
  L.normalizerMonoidHom.comp (Subgroup.inclusion
    ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance))

/-- Assertion (5) on the source action and original Sylow subgroup. -/
theorem MathieuSourceSetup.four_fixed_mem_source_sylow_image
    (c : MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hmodel : IsSmallRemainingComponent L) (F : Subgroup L) [IsKleinFour F]
    (hFS : F ≤ (((S : Subgroup H).map H.subtype).subgroupOf L))
    (a : MulAut L) (ha : a ∈ (MathieuSourceSetup.componentAction c).range)
    (hfix : ∀ x ∈ F, a x = x) :
    a ∈ (S : Subgroup H).map (MathieuSourceSetup.componentAction c) := by
  apply hmodel.four_fixed_mem_sylow_image (MathieuSourceSetup.componentAction c) S F _ a ha hfix
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨s, hs, he⟩ := hFS hx
  refine ⟨s, hs, ?_⟩
  ext y
  change (s : G) * (y : G) * (s : G)⁻¹ = (x : G) * (y : G) * (x : G)⁻¹
  change (s : G) = (x : G) at he
  rw [he]

omit [Finite G] in
/-- The actual component four-normalizer is S₄, with the original subtype. -/
theorem MathieuSourceSetup.four_normalizer
    (_c : MathieuSourceSetup H L M S z) (hmodel : IsSmallRemainingComponent L)
    (F : Subgroup G) (hFL : F ≤ L) [IsKleinFour F] :
    Nonempty (normalizer (F.subgroupOf L : Set L) ≃* Equiv.Perm (Fin 4)) := by
  let e := subgroupOfEquivOfLe hFL
  let : IsKleinFour (F.subgroupOf L) := {
    card_four := (Nat.card_congr e.toEquiv).trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv e).trans IsKleinFour.exponent_two }
  exact hmodel.four_normalizer (F.subgroupOf L)

/-- Source 2.5.12's actual centralizer containment. The only earlier premise
is C_H(L) ≤ S, supplied by the source component-centralizer/two-core result. -/
theorem MathieuSourceSetup.four_centralizer_le_source_sylow
    (c : MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hmodel : IsSmallRemainingComponent L)
    (hCL : H ⊓ centralizer (L : Set G) ≤ (S : Subgroup H).map H.subtype)
    (F : Subgroup G) [IsKleinFour F]
    (hFS : F ≤ (S : Subgroup H).map H.subtype) (hFL : F ≤ L) :
    H ⊓ centralizer (F : Set G) ≤ (S : Subgroup H).map H.subtype := by
  let e := subgroupOfEquivOfLe hFL
  let : IsKleinFour (F.subgroupOf L) := {
    card_four := (Nat.card_congr e.toEquiv).trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv e).trans IsKleinFour.exponent_two }
  intro x hx
  let xH : H := ⟨x, hx.1⟩
  let α := MathieuSourceSetup.componentAction c
  have hfix : ∀ y ∈ F.subgroupOf L, α xH y = y := by
    intro y hy
    apply Subtype.ext
    change x * (y : G) * x⁻¹ = (y : G)
    exact mul_inv_eq_iff_eq_mul.mpr (hx.2 y hy).symm
  have hm := MathieuSourceSetup.four_fixed_mem_source_sylow_image c hmodel
    (F.subgroupOf L) (fun y hy => hFS hy) (α xH) ⟨xH, rfl⟩ hfix
  obtain ⟨s, hs, he⟩ := hm
  have hk : α (s⁻¹ * xH) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
  have hkc : ((s⁻¹ * xH : H) : G) ∈ H ⊓ centralizer (L : Set G) := by
    refine ⟨(s⁻¹ * xH).property, ?_⟩
    intro l hl
    have hh := congrArg (fun a : MulAut L => a ⟨l, hl⟩) hk
    have hhv := congrArg Subtype.val hh
    change ((s⁻¹ * xH : H) : G) * l * ((s⁻¹ * xH : H) : G)⁻¹ = l at hhv
    exact (mul_inv_eq_iff_eq_mul.mp hhv).symm
  have hss : (s : G) ∈ (S : Subgroup H).map H.subtype := mem_map_of_mem H.subtype hs
  have hh := ((S : Subgroup H).map H.subtype).mul_mem hss (hCL hkc)
  simpa only [coe_mul, coe_inv, mul_inv_cancel_left] using hh

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
