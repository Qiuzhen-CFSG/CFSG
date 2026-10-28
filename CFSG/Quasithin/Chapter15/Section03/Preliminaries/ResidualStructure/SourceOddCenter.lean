module
public import Theory.GroupTheory.NormalOddCenter
public import Theory.GroupTheory.CComponent.QuotientLifting
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.SourceCommutator

/-!
# The original odd-central kernel in the orthogonal residual source

The star image of C_Y(V) is normal in M/O₂(M), and lies in the two commuting
normal subgroups Y* and C_M(V)*. It is therefore abelian. Triviality of the
ambient two-core makes its order odd. The preceding commutator calculation
also makes it centralize R_c*, so it lies in O(Z(C_M(V)* R_c*)).

This proves the second clause of 14.1.17(3) used by 15.3.7 from the original
local containment alone. Source: Aschbacher--Smith, printed pp.980,1122.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]

theorem source_star_odd_center (M Mc V : Subgroup G)
    (d : NaturalOrthogonalAction M V)
    (hC : M ⊓ centralizer (V : Set G) ≤ Mc) :
    ThreeAlternatives.star M (residualY M Mc ⊓ centralizer (V : Set G)) ≤
      ThreeAlternatives.oddCenterIn
        (ThreeAlternatives.star M (M ⊓ centralizer (V : Set G)) ⊔
          ThreeAlternatives.star M ((M ⊓ Mc).pCoreIn 2)) := by
  let Y := (residualY M Mc).subgroupOf M
  let C := d.actor.ker
  let q := QuotientGroup.mk' (pCore 2 M)
  let A := (Y ⊓ C).map q
  let K := ThreeAlternatives.star M (M ⊓ centralizer (V : Set G)) ⊔
    ThreeAlternatives.star M ((M ⊓ Mc).pCoreIn 2)
  let : Y.Normal := residualY_normal M Mc
  let : A.Normal := (inferInstance : (Y ⊓ C).Normal).map q (QuotientGroup.mk'_surjective _)
  have hCeq : (M ⊓ centralizer (V : Set G)).subgroupOf M = C := by
    rw [show C = d.actor.ker from rfl,d.ker_actor]
    ext x
    exact ⟨fun h => h.2,fun h => ⟨x.property,h⟩⟩
  have hAeq : ThreeAlternatives.star M (residualY M Mc ⊓ centralizer (V : Set G)) = A := by
    unfold ThreeAlternatives.star
    congr 1
    rw [show C = d.actor.ker from rfl,d.ker_actor]
    exact comap_inf _ _ _
  have hAC : A ≤ ThreeAlternatives.star M (M ⊓ centralizer (V : Set G)) := by
    change (Y ⊓ C).map q ≤ ((M ⊓ centralizer (V : Set G)).subgroupOf M).map q
    rw [hCeq]
    exact map_mono inf_le_right
  have hAY : A ≤ ThreeAlternatives.star M (residualY M Mc) := map_mono inf_le_left
  have hc := source_star_centralizes M Mc V d hC
  have hAK : A ≤ K := hAC.trans le_sup_left
  have hcentral : A ≤ centralizer (K : Set (ThreeAlternatives.StarGroup M)) := by
    apply le_centralizer_iff.mpr
    apply sup_le
    · exact hc.trans (centralizer_le (hAY.trans le_sup_left))
    · apply le_centralizer_iff.mpr
      exact hAC.trans (hc.trans (centralizer_le
        (show ThreeAlternatives.star M ((M ⊓ Mc).pCoreIn 2) ≤
          ThreeAlternatives.star M (residualY M Mc) ⊔
            ThreeAlternatives.star M ((M ⊓ Mc).pCoreIn 2) from le_sup_right)))
  rw [hAeq]
  exact normal_le_primeTo_center_of_centralizes A K
    (pCore_quotient_pCore_eq_bot 2) hAK hcentral

end CFSG.Quasithin.Chapter15.Section03
