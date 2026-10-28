module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefLift

/-!
# The 14.7.71 centralizer step on genuine source data

The original C-component condition supplies perfectness of K. The literal
K-image is A₅; the earlier order-two image of the chosen Uα supplies an
even involution, without requiring an involutory lift in H. ChiefLift then
proves [K,C_H(U)] ≤ U from the original intersection and normalizer bounds.

All 66–70 premises refer to the same supplied Uα. This discharges the
centralizer step, not the remaining placement and count of chief factors.
Source: Aschbacher–Smith 14.7.71, printed p.1075 (1 March 2004 manuscript).
-/

public section

open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] (d : Data T L V F W)

theorem source_centralizer_commutator_le
    (Uα : Subgroup G) (hUαH : Uα ≤ F.H)
    (hUQ : F.U ≤ F.H.pCoreIn 2)
    (hCQ : F.H ⊓ centralizer (F.U : Set G) ≤ F.H.pCoreIn 2)
    (hCN : F.H ⊓ centralizer (F.U : Set G) ≤ normalizer Uα)
    (h70 : F.U.relIndex Uα = 4)
    (h69 : Nat.card ((Uα.subgroupOf F.H).map d.qH) = 2)
    (h66 : (Uα.subgroupOf F.H).map d.qH ≤ ((K F).subgroupOf F.H).map d.qH) :
    ⁅K F, F.H ⊓ centralizer (F.U : Set G)⁆ ≤ F.U := by
  let := d.abelian
  let : (F.U.subgroupOf F.H).Normal :=
    normal_subgroupOf_of_le_normalizer d.conjugationSection.normalized
  let : ((K F).subgroupOf F.H).Normal :=
    normal_subgroupOf_of_le_normalizer (H_normalizes_K F)
  let := d.component.perfect
  let : Group.IsPerfect (K F) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (K_le_H F)).toMonoidHom)
    (subgroupOfEquivOfLe (K_le_H F)).surjective
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card'
    (G := (Uα.subgroupOf F.H).map d.qH) 2 (by rw [h69])
  obtain ⟨t,ht,hte⟩ := a.property
  have htord : orderOf (d.qH t) = 2 := by rw [hte]; exact (orderOf_coe a).trans ha
  have heven : d.qH t ∈ alternatingGroup (Fin 5) := by
    rw [← d.K_image]
    exact h66 (mem_map_of_mem d.qH ht)
  exact centralizer_commutator_le F.H (F.H.pCoreIn 2) F.U Uα (K F) d.qH
    d.qH_surjective d.qH_ker (pCoreIn_le 2 F.H) (isPGroup_pCoreIn 2 F.H) hUQ
    (K_le_H F) (fun k => by
      rw [← d.K_image]
      exact mem_map_of_mem d.qH k.property)
    hCQ hCN hUαH h70 h69 t ht htord heven

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame
