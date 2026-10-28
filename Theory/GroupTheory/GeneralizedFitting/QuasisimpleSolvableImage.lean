module
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter
public import Theory.GroupTheory.PerfectCentralizerLift

/-!
# Quasisimple generalized Fitting subgroups under solvable kernels

A solvable normal kernel centralizes a normal component. Perfect-centralizer
lifting then makes the image of a quasisimple generalized Fitting subgroup
self-centralizing. Every other component and the Fitting subgroup lie in that
image, which is therefore the target's full generalized Fitting subgroup.

The original quotient comparison in Aschbacher--Smith 13.2.12 uses this on
the actual map from the prime-to-three quotient to the faithful point-span
action (printed p.882). No identification of those quotients is assumed.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

/-- A normal quasisimple subgroup containing its centralizer is F*. -/
theorem generalizedFitting_eq_of_quasisimple_centralizer_le
    (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hC : centralizer (L : Set G) ≤ L) : generalizedFitting G = L := by
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hL : IsComponent G L := ⟨(inferInstance : L.Normal).isSubnormal, inferInstance⟩
  apply le_antisymm _ (component_le_generalizedFitting G L hL)
  apply sup_le
  · exact (le_centralizer_iff.mp (hL.le_centralizer_of_solvable_normal _)).trans hC
  · apply sSup_le
    intro K hK
    by_cases hk : K = L
    · exact hk.le
    · exact (commutator_eq_bot_iff_le_centralizer.mp
        (hK.commutator_eq_bot_of_ne hL hk)).trans hC

/-- A solvable kernel preserves quasisimple F*, with its literal image. -/
theorem quasisimple_generalizedFitting_image_of_solvable_kernel
    [IsQuasisimple (generalizedFitting G)]
    (f : G →* H) (hf : Function.Surjective f) [Group.IsSolvable f.ker] :
    (generalizedFitting G).map f = generalizedFitting H ∧
      IsQuasisimple (generalizedFitting H) := by
  let L := generalizedFitting G
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hL : IsComponent G L := ⟨(inferInstance : L.Normal).isSubnormal, inferInstance⟩
  have hk : f.ker ≤ centralizer (L : Set G) :=
    le_centralizer_iff.mp (hL.le_centralizer_of_solvable_normal f.ker)
  have hn : L.map f ≠ ⊥ := by
    intro hh
    have hle : L ≤ f.ker := (Subgroup.map_eq_bot_iff L).mp hh
    have hs : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
      (f := inclusion hle) (inclusion_injective hle)
    exact Group.IsPerfect.not_isSolvable L hs
  let : Nontrivial (L.map f) := (nontrivial_iff_ne_bot _).mpr hn
  let : IsQuasisimple (L.map f) :=
    IsQuasisimple.of_surjective (f.subgroupMap L) (f.subgroupMap_surjective L)
  let : (L.map f).Normal := Normal.map inferInstance f hf
  have hC : centralizer (L.map f : Set H) ≤ L.map f := by
    intro y hy
    obtain ⟨x,rfl⟩ := hf y
    have hx : x ∈ centralizer (L : Set G) :=
      (comap_centralizer_map_eq_of_perfect f L hk).le hy
    exact mem_map_of_mem f (centralizer_generalizedFitting_le G hx)
  have he := generalizedFitting_eq_of_quasisimple_centralizer_le (L.map f) hC
  exact ⟨he.symm,he ▸ inferInstance⟩
end Theory.GroupTheory
