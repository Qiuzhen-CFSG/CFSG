module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Defs
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.CentralProduct
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.ModuleActions.Natural
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.ModuleActions.Sections
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.ModuleActions.Extension
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.ModuleActions.Indecomposable
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Commutators.NaturalHead
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.CoreEquality
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.FixedPlane

/-!
# Module calculations for J.2.5–6

This module proves all three fields of `OuterActionData` on the original
Ru2 quotient marking. The natural action is free at every outer involution.
The natural head gives the actual equivariant surjection Q/U → Q/HC with
two-dimensional HC/U kernel, fixed by A₅ by J.2.2(3). Indecomposability
forces an outer involution to move a kernel vector, so both the kernel and
the natural head are free, and hence so is Q/U.

The decomposition HC = C_Q(B)U transports kernel movement to a displacement
of an actual element of C_Q(B) outside Z. `outerActionData_of_naturalHead`
retains the permitted preceding-source inputs. `outerActionData_of_centralProduct`
discharges Q≤K, the natural head and [K,HC]≤U using the proved J.2.2
components. Only `CentralProductData` remains explicit, with producer
`qt-j12-fusion-commutators`; the final J.2.5–6 assembly remains in
`qt-j12-fusion-outer`.

Source: Aschbacher–Smith, J.2.2(3) and J.2.5–6, printed pp.432, 434–435
(PDF pp.443, 445–446 of `refs/quasithin.pdf`).
-/

public section

open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.Fusion.Outer
variable {G : Type*} [Group G] [Finite G]

/-- The J.2.5–6 action calculations from the marked natural head,
J.2.2(1)'s Q≤K, J.2.2(3)'s fixed-kernel assertion and the central product.
No freeness or nontrivial outer action is assumed. -/
theorem outerActionData_of_naturalHead (d : LocalSetup G)
    (B : Sylow 3 d.toTypeRuSetup.L₁) (head : NaturalHead d.toTypeRuSetup)
    (cp : CentralProductData d.toTypeRuSetup B)
    (hQK : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.K)
    (hfixed : ∀ q ∈ d.toTypeRuSetup.HC, ∀ k ∈ d.toTypeRuSetup.K,
      ⁅k, q⁆ ∈ d.toTypeRuSetup.U) :
    OuterActionData d.toTypeRuSetup B where
  natural_free := natural_free d.toTypeRuSetup hQK
  six_free i hi hi2 := by
    have ht := quotientMap_not_alternating d.toTypeRuSetup hQK i hi
    have ht2 := quotientMap_involution d.toTypeRuSetup i hi2
    exact head.six_free_of_kernel_moved d _ ht ht2
      (head.sixProjection_kernel_moved d hfixed _ ht ht2)
  quaternion_moved i hi hi2 := by
    let iH : d.toTypeRuSetup.H := ⟨(i : G), i.property.1⟩
    have ht := quotientMap_not_alternating d.toTypeRuSetup hQK iH hi
    have ht2 := quotientMap_involution d.toTypeRuSetup iH hi2
    exact head.quaternion_moved_of_kernel_moved d B cp iH
      (head.sixProjection_kernel_moved d hfixed _ ht ht2)

/-- All module-action obligations for the actual local setup, with the
earlier J.2.2 premises discharged. The central-product input is produced
by the independent J.2.4 branch. -/
theorem outerActionData_of_centralProduct (d : LocalSetup G)
    (B : Sylow 3 d.toTypeRuSetup.L₁)
    (cp : CentralProductData d.toTypeRuSetup B) :
    OuterActionData d.toTypeRuSetup B :=
  outerActionData_of_naturalHead d B d.fusionNaturalHead cp d.Q_le_K
    (fun q hq k hk => d.HC_commutator_K_mem_U ⟨q, hq⟩ ⟨k, hk⟩)

end CFSG.Quasithin.ChapterJ.Fusion.Outer
