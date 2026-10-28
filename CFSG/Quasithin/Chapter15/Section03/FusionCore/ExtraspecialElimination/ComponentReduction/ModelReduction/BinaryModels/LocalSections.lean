module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ActionGeneration
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.GroupTheory.QuotientIntersection
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The literal component and Sylow sections in 15.3.49(l)

The source uses T₀ = T ∩ L after identifying L₀ with L. Subnormality of
L inside H makes T₀ Sylow in L. Because O₂(H) is contained in T, the image
of this intersection equals T* ∩ L*. The quotient of the intrinsic
component by its own two-core is multiplicatively equivalent to L*;
quasisimplicity therefore transports to the input of ActionGeneration.

These are quotient and Sylow bridges. They do not identify the component
orbit with L or assert any model or parabolic classification.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1144,
proof of 15.3.49(k)–(l), and A.1.16 for the kernel-containing intersection.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter1
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A Sylow subgroup contains the quotient kernel, so the literal intersection has the expected star image. -/
theorem starImage_inter_sylow (H T L : Subgroup G) (hT : IsSylowIn 2 T H) :
    starImage H (T ⊓ L) = starImage H T ⊓ starImage H L := by
  obtain ⟨S, rfl⟩ := hT
  have hcore : pCore 2 H ≤ ((S : Subgroup H).map H.subtype).subgroupOf H := by
    change pCore 2 H ≤ ((S : Subgroup H).map H.subtype).comap H.subtype
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    exact pCore_isPGroup.le_sylow_of_normal S
  unfold starImage Subgroup.subgroupOf
  rw [comap_inf, inf_comm, map_inf_of_ker_le _ _ _ (by
    rw [QuotientGroup.ker_mk']; exact hcore), inf_comm]

/-- Identify the intrinsic component quotient with its image in the local quotient. -/
noncomputable def componentStarEquiv (H L : Subgroup G) (hLH : L ≤ H)
    (hL : (L.subgroupOf H).IsCComponent) :
    (L ⧸ pCore 2 L) ≃* starImage H L :=
  (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLH).symm
    (pCore_map_iso 2 (subgroupOfEquivOfLe hLH).symm)).trans
      (cComponentTwoCoreQuotientEquiv hL)

/-- Transport source quasisimplicity to the star image used by ActionGeneration. -/
theorem starImage_quasisimple (H L : Subgroup G) (hLH : L ≤ H)
    (hL : (L.subgroupOf H).IsCComponent)
    [Theory.GroupTheory.IsQuasisimple (L ⧸ pCore 2 L)] :
    Theory.GroupTheory.IsQuasisimple (starImage H L) :=
  Theory.GroupTheory.IsQuasisimple.of_mulEquiv (componentStarEquiv H L hLH hL)

/-- Transport relative Sylow membership to the actual local quotient. -/
theorem starImage_isSylowIn (H T L : Subgroup G)
    (hTH : T ≤ H) (hLH : L ≤ H) (hT : IsSylowIn 2 T L) :
    IsSylowIn 2 (starImage H T) (starImage H L) := by
  have hi : IsSylowIn 2 (T.subgroupOf H) (L.subgroupOf H) := by
    apply (IsSylowIn.map_iff H.subtype H.subtype_injective).mp
    simpa only [map_subgroupOf_eq_of_le hTH, map_subgroupOf_eq_of_le hLH] using hT
  exact CFSG.Quasithin.Chapter1.Section02.IndexTwo.isSylowIn_map hi
    (QuotientGroup.mk' (pCore 2 H))

/-- The literal T₀ = T ∩ L is Sylow in the component, and T₀* is Sylow in L*. -/
theorem component_inter_sylow (H T L : Subgroup G)
    (hT : IsSylowIn 2 T H) (hLH : L ≤ H) (hL : (L.subgroupOf H).IsCComponent) :
    IsSylowIn 2 (T ⊓ L) L ∧
      IsSylowIn 2 (starImage H (T ⊓ L)) (starImage H L) := by
  have h := CFSG.Quasithin.Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    hT hLH hL.subnormal
  exact ⟨h, starImage_isSylowIn H (T ⊓ L) L (inf_le_right.trans hLH) hLH h⟩


end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels
