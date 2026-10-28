module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Marker
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# The cubic residual for either surviving marker

If the two-residual of the faithful centralizer quotient has order three,
that quotient is a {2,3}-group. Its two-residual and prime-to-three
residual therefore coincide. Lifting their equality through the literal
module centralizer proves equality of their moved subgroups. This uses
neither a cyclic marker nor a four-dimensional module.

Source: Aschbacher--Smith 15.1.24(3), printed p.1101.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
variable {G : Type*} [Group G] [Finite G]

private theorem twoThree_of_residual_card_three {D : Type*} [Group D] [Finite D]
    (hc : Nat.card (pResidual 2 D) = 3) : IsPiGroup twoThreePrimes D := by
  apply IsPiGroup.of_normal_subgroup_and_quotient (pResidual 2 D)
  · intro p hp
    rw [hc] at hp
    exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp hp |>.resolve_left p.property.ne_one)
  · apply (IsPiGroup_iff _ _).mpr
    intro p hp
    obtain ⟨n,hn⟩ := (isPGroup_quotient_pResidual (G := D) 2).exists_card_eq
    rw [hn] at hp
    exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (p.property.dvd_of_dvd_pow hp) |>.resolve_left
      p.property.ne_one)

/-- Equality of the original moved subgroups follows just from the faithful
residual order. The quotient is by C_M(V), not by a two-core. -/
theorem caseI_cubic_commutator_of_residual_card_three
    {M V Z1 : Subgroup G} (hn : M ≤ normalizer (V : Set G)) (hZ : Z1 ≤ V)
    (hc : letI := caseI_module_centralizer_normal (Z1 := Z1) hn
      Nat.card (pResidual 2 ((M ⊓ centralizer (Z1 : Set G) : Subgroup G) ⧸
        (M ⊓ centralizer (V : Set G)).subgroupOf (M ⊓ centralizer (Z1 : Set G)))) = 3) :
    ⁅V,(primeToResidual 3 (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
        (M ⊓ centralizer (Z1 : Set G)).subtype⁆ =
      ⁅V,(pResidual 2 (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
        (M ⊓ centralizer (Z1 : Set G)).subtype⁆ := by
  let C := M ⊓ centralizer (Z1 : Set G)
  let N := M ⊓ centralizer (V : Set G)
  let K := N.subgroupOf C
  let : K.Normal := caseI_module_centralizer_normal hn
  let q := QuotientGroup.mk' K
  have he : (primeToResidual 3 C).map q = (pResidual 2 C).map q := by
    rw [map_primeToResidual_of_surjective 3 q (QuotientGroup.mk'_surjective K),
      map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective K)]
    exact (twoResidual_eq_primeToResidual_three (twoThree_of_residual_card_three hc)).symm
  have he' := congrArg (Subgroup.comap q) he
  simp only [comap_map_eq] at he'
  have hker : q.ker = K := QuotientGroup.ker_mk' K
  rw [hker] at he'
  have hNC : N ≤ C := inf_le_inf_left M (centralizer_le hZ)
  have hsup := congrArg (Subgroup.map C.subtype) he'
  rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hNC] at hsup
  let Y := (primeToResidual 3 C).map C.subtype
  let R := (pResidual 2 C).map C.subtype
  have hY : Y ≤ normalizer (V : Set G) := ((map_subtype_le _).trans inf_le_left).trans hn
  have hR : R ≤ normalizer (V : Set G) := ((map_subtype_le _).trans inf_le_left).trans hn
  change ⁅V,Y⁆ = ⁅V,R⁆
  calc
    ⁅V,Y⁆ = ⁅V,N ⊔ Y⁆ := commutator_eq_of_centralizing_sup rfl inf_le_right hY
    _ = ⁅V,N ⊔ R⁆ := by rw [sup_comm N Y,hsup,sup_comm R N]
    _ = ⁅V,R⁆ := (commutator_eq_of_centralizing_sup rfl inf_le_right hR).symm

/-- The same cubic residual calculation applies to a marker of either size. -/
theorem CaseIPreExclusionMarker.cubic_commutator
    {T : Sylow 2 G} {M V : Subgroup G} {hn : M ≤ normalizer (V : Set G)}
    (m : CaseIPreExclusionMarker T M V hn) (hp : m.prime = 3) :
    ⁅V,(primeToResidual 3 (M ⊓ centralizer (m.Z1 : Set G) : Subgroup G)).map
      (M ⊓ centralizer (m.Z1 : Set G)).subtype⁆ = m.movingPlane := by
  exact caseI_cubic_commutator_of_residual_card_three hn
    (m.marked_fixed.trans inf_le_left) (m.residual_card.trans hp)

end CFSG.Quasithin.Chapter15.Section01
