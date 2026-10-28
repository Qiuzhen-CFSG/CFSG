module

public import Theory.SpecificGroups.ReeTwo.ParabolicIndexTwo.Kernels

/-!
# Derived subgroups and their centralizers in the index-two Ree locals

The intrinsic two-cores of the core and mixed kernels have derived subgroup
the embedded elementary tail E of order 32, and their entire local groups
centralize E precisely in E. The parity kernel instead retains the full core
and its order-64 derived centralizer. The proof transports the computed omega
commutator through the actual inclusions, then intersects the already computed
ambient derived centralizer with each character kernel.

Here a commutator of subgroups is computed in its displayed local group;
no ambient normality is substituted for relative normality. These results
supply the corresponding local calculations for quasithin 14.2.21, printed
p.989, and Parrott (1972), printed p.672. Ambient model comparisons, quotient
actions and involution fusion remain separate from these calculations.
-/

@[expose] public section
open Subgroup
namespace ReeTwo.Centralizer.IndexTwo

/-- The embedded omega subgroup has the same derived tail as the full core. -/
theorem omega_commutator : ⁅omega,omega⁆ = derived := by
  rw [omega, ← Subgroup.map_commutator, Core.omega_commutator]
  rfl

/-- The embedded derived tail lies in the embedded omega subgroup. -/
theorem derived_le_omega : derived ≤ omega := by
  exact Subgroup.map_mono Core.derived_lt_omega.le

/-- The embedded derived tail lies in the full core. -/
theorem derived_le_core : derived ≤ core := Subgroup.map_le_range _ _

/-- The derived subgroup of the alternative two-core, viewed in the local group, is the actual tail. -/
theorem alternative_derived (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) :
    ⁅pCore 2 χ.ker, pCore 2 χ.ker⁆ = derived.subgroupOf χ.ker := by
  apply Subgroup.map_injective χ.ker.subtype_injective
  rw [Subgroup.map_commutator, alternative_pCore χ hχ,
    Subgroup.map_subgroupOf_eq_of_le (omega_le_kernel χ hχ), omega_commutator,
    Subgroup.map_subgroupOf_eq_of_le (derived_le_omega.trans (omega_le_kernel χ hχ))]

/-- The derived subgroup of either alternative two-core has order 32. -/
theorem alternative_derived_card (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) :
    Nat.card (⁅pCore 2 χ.ker, pCore 2 χ.ker⁆ : Subgroup χ.ker) = 32 := by
  rw [alternative_derived χ hχ,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (derived_le_omega.trans (omega_le_kernel χ hχ))).toEquiv]
  exact Centralizer.derived_card

/-- The derived subgroup of either alternative two-core is elementary abelian. -/
theorem alternative_derived_elementary (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) :
    IsElementaryAbelian 2 (⁅pCore 2 χ.ker, pCore 2 χ.ker⁆ : Subgroup χ.ker) := by
  rw [alternative_derived χ hχ]
  let : IsElementaryAbelian 2 derived := Centralizer.derived_elementary
  exact IsElementaryAbelian.subgroupOf (derived_le_omega.trans (omega_le_kernel χ hχ))

private theorem centralizer_restrict (L : Subgroup Centralizer) (hL : derived ≤ L) :
    centralizer (derived.subgroupOf L : Set L) =
      (centralizer (derived : Set Centralizer)).subgroupOf L := by
  ext x
  constructor
  · intro hx y hy
    exact congrArg Subtype.val (hx ⟨y,hL hy⟩ hy)
  · intro hx y hy
    exact Subtype.ext (hx (y : Centralizer) hy)

/-- The tail is self-centralizing in the whole alternative local group. -/
theorem alternative_centralizer_derived (χ : Centralizer →* FiveFour.Cyclic 2)
    (hχ : χ = coreCharacter ∨ χ = mixedCharacter) :
    centralizer ((⁅pCore 2 χ.ker, pCore 2 χ.ker⁆ : Subgroup χ.ker) : Set χ.ker) =
      ⁅pCore 2 χ.ker, pCore 2 χ.ker⁆ := by
  rw [alternative_derived χ hχ,
    centralizer_restrict χ.ker (derived_le_omega.trans (omega_le_kernel χ hχ)),
    centralizer_derived_eq_map]
  ext x
  constructor
  · rintro ⟨y,hy,he⟩
    have hw : y ∈ omega₁ Core (p := 2) := by
      rw [← Core.binaryCharacter_ker_eq_omega]
      change Core.binaryCharacter y = 1
      rw [← alternative_inl χ hχ, he]
      exact x.property
    refine ⟨y,?_,he⟩
    exact Core.omega_inf_centralizer_derived ▸ (show y ∈ omega₁ Core (p := 2) ⊓
      centralizer (commutator Core : Set Core) from ⟨hw,hy⟩)
  · rintro ⟨y,hy,he⟩
    refine ⟨y,?_,he⟩
    have hm : y ∈ omega₁ Core (p := 2) ⊓ centralizer (commutator Core : Set Core) :=
      Core.omega_inf_centralizer_derived.symm ▸ hy
    exact hm.2

/-- The parity two-core has the original derived tail. -/
theorem parity_derived : ⁅pCore 2 parityLocal, pCore 2 parityLocal⁆ =
    derived.subgroupOf parityLocal := by
  apply Subgroup.map_injective parityLocal.subtype_injective
  rw [Subgroup.map_commutator, ← core_subgroupOf_eq_pCore,
    Subgroup.map_subgroupOf_eq_of_le core_le_parityLocal,
    ← derived_eq_core_commutator,
    Subgroup.map_subgroupOf_eq_of_le (derived_le_core.trans core_le_parityLocal)]

/-- The parity local group retains the full centralizer of the original derived tail. -/
theorem parity_centralizer_derived :
    centralizer ((⁅pCore 2 parityLocal, pCore 2 parityLocal⁆ : Subgroup parityLocal) : Set parityLocal) =
      (centralizer (derived : Set Centralizer)).subgroupOf parityLocal := by
  rw [parity_derived]
  exact centralizer_restrict parityLocal (derived_le_core.trans core_le_parityLocal)

/-- The derived centralizer in the parity local group has order 64. -/
theorem parity_centralizer_derived_card :
    Nat.card (centralizer ((⁅pCore 2 parityLocal, pCore 2 parityLocal⁆ : Subgroup parityLocal) : Set parityLocal)) = 64 := by
  rw [parity_centralizer_derived]
  have hle : centralizer (derived : Set Centralizer) ≤ parityLocal := by
    rw [centralizer_derived_eq_map]
    exact (Subgroup.map_le_range _ _).trans core_le_parityLocal
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
  exact Centralizer.centralizer_derived_card

end ReeTwo.Centralizer.IndexTwo
