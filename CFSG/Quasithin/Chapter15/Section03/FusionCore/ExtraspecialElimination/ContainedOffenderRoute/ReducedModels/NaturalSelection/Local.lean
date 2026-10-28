module
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.LateClassification
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.FieldExclusion
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# The local subgroup of the late offender actor

Intersect Y₀*T* with the actual normal offender-generated actor. The ambient
Sylow subgroup restricts to a Sylow subgroup of that actor. The cubic element
of Y₀ survives the star quotient and lies in the same local subgroup, because
containment and orbit collapse put Y₀ inside its component.

Source: Aschbacher–Smith, proof of 15.3.49(k)–(l), printed p.1144
(combined manuscript, 1 March 2004).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
universe u
namespace Input
variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : Input κ H M Y V Y0 T ZS Z E L upper)
include d

/-- The genuine local subgroup inside the late actor. -/
noncomputable abbrev lateLocal : Subgroup (lateActor d.placed.action) :=
  (starImage H Y0 ⊔ starImage H T).subgroupOf (lateActor d.placed.action)

/-- This local subgroup contains a Sylow subgroup of the late actor, since
the latter is normal in the original star group. -/
theorem lateLocal_contains_sylow :
    ∃ S : Sylow 2 (lateActor d.placed.action), (S : Subgroup _) ≤ d.lateLocal := by
  obtain ⟨P, hP⟩ := d.sylowIn
  let Q := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hQ : (Q : Subgroup (H ⧸ pCore 2 H)) = starImage H T := by
    rw [← hP]
    change (P : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)) =
      (((P : Subgroup H).map H.subtype).comap H.subtype).map _
    rw [comap_map_eq_self_of_injective H.subtype_injective]
  let := lateActor_normal d.placed.action
  obtain ⟨S, hS⟩ := Q.exists_subgroupOf_eq_of_normal (lateActor d.placed.action)
  exact ⟨S, hS.trans_le (by rw [hQ]; exact comap_mono le_sup_right)⟩

/-- The cubic element survives the quotient and lies in this same local
subgroup, through containment in the actual component. -/
theorem lateLocal_three_dvd
    (sections : EarlierComponentSections κ)
    (orbits : BinaryModels.OrbitClosure.EarlierOrbitAlternative κ) :
    3 ∣ Nat.card d.lateLocal := by
  have hyL := (d.structure_of_earlier sections orbits).2.1
  have hyP : starImage H Y0 ≤ lateActor d.placed.action :=
    (map_mono (comap_mono hyL)).trans (d.component_le_late_actor sections orbits)
  obtain ⟨y, hy⟩ := LargerFields.RankOne.star_cubic H Y0 d.y_le d.quotient_card
  let y' : d.lateLocal := ⟨⟨y.val, hyP y.property⟩, (show starImage H Y0 ≤ starImage H Y0 ⊔ starImage H T from le_sup_left) y.property⟩
  have hy' : orderOf y' = 3 := by
    rw [← Subgroup.orderOf_coe y', ← Subgroup.orderOf_coe (y' : lateActor d.placed.action)]
    exact (Subgroup.orderOf_coe y).trans hy
  exact hy' ▸ orderOf_dvd_natCard y'

end Input
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
