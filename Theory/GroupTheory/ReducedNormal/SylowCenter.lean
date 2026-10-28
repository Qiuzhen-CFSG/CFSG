module
public import Theory.GroupTheory.ReducedNormal.Inheritance
public import Theory.GroupTheory.PGroup.OmegaCenterIn
/-!
# The Sylow omega-center lies in the reduced subgroup

A central elementary abelian subgroup has trivial conjugation quotient and
is reduced. In a group of characteristic two, reduced-subgroup inheritance
from a Sylow overgroup therefore puts the original omega-center of the Sylow
subgroup inside R₂(G). This is the inclusion from B.2.14 needed in13.1.5.
Source: Aschbacher--Smith, B.2.13--14, printed p.78.
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem isPReduced_of_le_center_for_omega {p : ℕ} (Z : Subgroup G)
    (hz : Z ≤ center G) [IsElementaryAbelian p Z] : IsPReduced p Z := by
  have hn : Z.Normal := by
    refine ⟨fun z hz' g => ?_⟩
    have hc := mem_center_iff.mp (hz hz') g
    simpa only [hc, mul_inv_cancel_right] using hz'
  refine ⟨hn, inferInstance, ?_⟩
  let := hn
  apply bot_unique
  intro x _
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (centralizer (Z : Set G)) x
  apply (QuotientGroup.eq_one_iff g).mpr
  intro z hZ
  exact (mem_center_iff.mp (hz hZ) g).symm

theorem sylow_omegaCenter_le_reduced [Finite G] (T : Sylow 2 G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    omegaCenterIn (T : Subgroup G) ≤ reducedTwoSubgroup G := by
  let Z : Subgroup T := (omega₁ (center T) (p := 2)).map (center T).subtype
  let : IsElementaryAbelian 2 (omega₁ (center T) (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.map _
  have hz : Z ≤ center T := map_subtype_le _
  have hr : IsPReduced 2 Z := isPReduced_of_le_center_for_omega Z hz
  have hi := reducedPSubgroup_map_le_of_sylow_le T (T : Subgroup G) le_rfl hc
  exact (map_mono hr.le_reducedPSubgroup).trans hi
end Theory.GroupTheory

