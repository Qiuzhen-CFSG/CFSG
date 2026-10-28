module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.FittingPairExclusion
public import Theory.GroupTheory.ConjugatePairSpanKernel
/-!
# The C.5.12 small-span obstruction with its kernel proved

The characteristic-two ambient group and its actual core commutator imply
both invariance of U+Uᵍ under D=⟨K,Kᵍ⟩ and C_D(U+Uᵍ)≤O₂(D). The order
sixteen of U then supplies the eight-dimensional bound, so every original
C-component of D/O₂(D) is quasisimple. The distinct ambient and action
quotients are retained; no faithful action of D/O₂(D) is assumed.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
variable {G : Type*} [Group G] [Finite G]
theorem pair_span_quasisimple_from_ambient_core
    {κ : GroupClass} (K U : Subgroup G) (g : G)
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hcore : ⁅pCore 2 G,K⁆ = U) (hUK : U ≤ K) (hU : Nat.card U = 16)
    (hD : IsSQTK κ (K ⊔ K.conjBy g : Subgroup G))
    [IsElementaryAbelian 2 (U ⊔ U.conjBy g : Subgroup G)]
    (L : Subgroup ((K ⊔ K.conjBy g : Subgroup G) ⧸ pCore 2 (K ⊔ K.conjBy g : Subgroup G)))
    (hL : L.IsCComponent) : IsQuasisimple L := by
  let D := K ⊔ K.conjBy g
  let W := U ⊔ U.conjBy g
  have hWD : W ≤ D := sup_le_sup hUK (map_mono hUK)
  have hk := conjugate_pair_span_kernel K U g hchar hcore
  have hker : centralizer (W.subgroupOf D : Set D) ≤ pCore 2 D := by
    intro a ha
    apply hk.2.2
    intro w hw
    exact congrArg D.subtype (ha ⟨w,hWD hw⟩ hw)
  exact pair_span_quasisimple D hD U hU g hWD hk.1 hker L hL
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
