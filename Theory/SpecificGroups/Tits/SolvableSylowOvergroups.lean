module
public import Theory.SpecificGroups.Tits.ProperSylowOvergroups
public import Theory.GroupTheory.SolvableSylowOvergroups
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.TwoGroupExclusion.Solvability

/-!
# Solvable proper Sylow overgroups in the Tits group

The checked double-coset coverage places every proper overgroup of the
marked Sylow in one of the two full parabolics. The first parabolic has
a cyclic subgroup of order five and index 2¹¹, so the proved solvability
theorem for an abelian subgroup of prime-power index applies. The second
has a two-subgroup of index three. Thus both are solvable. Sylow conjugacy
and the actual finite-image isomorphism give the intrinsic result on the
Parrott carrier used in Theorem C.

This removes the Tits endpoint in the containing-component argument of
Aschbacher–Smith 5.2.2, printed p.648, using Parrott (1972), §5, p.683.
No new finite enumeration or parabolic classification premise is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Tits.ProperSylowOvergroups
open ExceptionalParabolics

private theorem first_isSolvable : Group.IsSolvable first := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let P : Sylow 5 first := Classical.choice inferInstance
  have hc : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, ReeLocalBlockOrders.first_card]
    decide +kernel
  let : IsCyclic P := isCyclic_of_prime_card hc
  have hi : (P : Subgroup first).index = 2 ^ 11 := by
    have he := (P : Subgroup first).card_mul_index
    rw [hc, ReeLocalBlockOrders.first_card] at he
    omega
  exact (P : Subgroup first).isSolvable_of_isMulCommutative_of_prime_power_index
    Nat.prime_two hi

private theorem second_isSolvable : Group.IsSolvable second := by
  have hS : IsPGroup 2 S := IsPGroup.of_card (n := 11) (by simpa using sylow_card)
  let : Group.IsNilpotent (S.subgroupOf second) := hS.comap_subtype.isNilpotent
  apply (S.subgroupOf second).isSolvable_of_index_le_four
  rw [RelativeSecondBlockLayers.second_sylow_index]
  decide

/-- The two full marked parabolics are solvable, so exhaustive placement
makes every proper full-Sylow overgroup solvable on the finite carrier. -/
theorem atlas_solvableSylowOvergroups : SolvableSylowOvergroups Atlas1600Group := by
  intro Q H hQH hH
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Atlas1600Group Q atlas1600SylowTwo
  let a := MulAut.conj g
  let X := H.map a.toMonoidHom
  have hX : X ≠ ⊤ := by
    intro he
    apply hH
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [map_top_of_surjective a.toMonoidHom a.surjective]
    exact he
  have hSX : atlas1600SylowTwoSubgroup ≤ X := by
    have hh : (Q : Subgroup Atlas1600Group).map a.toMonoidHom = atlas1600SylowTwoSubgroup := by
      change ((g • Q : Sylow 2 Atlas1600Group) : Subgroup Atlas1600Group) = _
      rw [hg,atlas1600SylowTwo_coe]
    rw [←hh]
    exact map_mono hQH
  have hsol : Group.IsSolvable X := by
    rcases ConverseLocalCoverage.le_first_or_second X hX hSX with hf | hs
    · let := first_isSolvable
      exact Group.isSolvable_of_isSolvable_injective (inclusion_injective hf)
    · let := second_isSolvable
      exact Group.isSolvable_of_isSolvable_injective (inclusion_injective hs)
  let : Group.IsSolvable (H.map a.toMonoidHom) := hsol
  exact Group.isSolvable_of_isSolvable_injective
    (f := (H.equivMapOfInjective a.toMonoidHom a.injective).toMonoidHom)
    (H.equivMapOfInjective a.toMonoidHom a.injective).injective

/-- The same conclusion on the literal Parrott carrier of Theorem C. -/
theorem solvableSylowOvergroups : SolvableSylowOvergroups ParrottGroup :=
  SolvableSylowOvergroups.of_equiv parrottFiniteImageEquiv atlas_solvableSylowOvergroups
end Tits.ProperSylowOvergroups
