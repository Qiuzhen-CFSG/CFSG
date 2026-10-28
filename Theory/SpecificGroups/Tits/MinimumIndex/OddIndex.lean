module

public import Theory.SpecificGroups.Tits.ConverseLocalCoverage
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.Orders
import Mathlib.Tactic.NormNum

/-!
# Odd-index subgroups of the concrete Tits group

A Sylow two-subgroup of an odd-index subgroup is Sylow in the ambient group.
Conjugate it to the marked Sylow subgroup and apply the proved double-coset
and generation certificates in `ConverseLocalCoverage`. Every proper
Sylow overgroup lies in one of the two marked parabolics, whose orders are
10240 and 6144. Lagrange's theorem then gives the sharper index bound 1755.

Source: the certified Parrott (1972), §5, p.683 construction used by
`ConverseLocalCoverage`; compare the parabolic entries in the primary ATLAS
Tits page, https://brauer.maths.qmul.ac.uk/Atlas/exc/TF42/.
The even-index case of the minimum-index theorem is separate.
-/

namespace Tits
open Subgroup ExceptionalParabolics
open scoped Pointwise

private theorem exists_conjugate_le_parabolic_of_odd_index
    (L : Subgroup Atlas1600Group) (hL : L ≠ ⊤) (hodd : ¬ 2 ∣ L.index) :
    ∃ g : Atlas1600Group,
      L.map (MulAut.conj g).toMonoidHom ≤ first ∨
      L.map (MulAut.conj g).toMonoidHom ≤ second := by
  let P : Sylow 2 L := Classical.choice inferInstance
  let Q : Sylow 2 Atlas1600Group :=
    (P.isPGroup'.map L.subtype).toSylow (by
      rw [Subgroup.index_map_subtype]
      exact Nat.prime_two.not_dvd_mul P.not_dvd_index hodd)
  have hQL : (Q : Subgroup Atlas1600Group) ≤ L := Subgroup.map_subtype_le _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Atlas1600Group Q atlas1600SylowTwo
  let L' := L.map (MulAut.conj g).toMonoidHom
  have hproper : L' ≠ ⊤ := by
    intro he
    apply hL
    apply Subgroup.index_eq_one.mp
    rw [← Subgroup.index_map_of_bijective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).bijective L]
    change L'.index = 1
    rw [he, Subgroup.index_top]
  have hS : atlas1600SylowTwoSubgroup ≤ L' := by
    rw [← atlas1600SylowTwo_coe, ← hg]
    change (Q : Subgroup Atlas1600Group).map (MulAut.conj g).toMonoidHom ≤ L'
    exact Subgroup.map_mono hQL
  exact ⟨g, ConverseLocalCoverage.le_first_or_second L' hproper hS⟩

/-- Containment of an actual conjugate in either marked parabolic bounds
the subgroup order by 10240. -/
public theorem atlas1600_subgroup_card_le_of_conjugate_parabolic (L : Subgroup Atlas1600Group)
    (g : Atlas1600Group)
    (hg : L.map (MulAut.conj g).toMonoidHom ≤ first ∨
      L.map (MulAut.conj g).toMonoidHom ≤ second) : Nat.card L ≤ 10240 := by
  rcases hg with h | h
  · have hc := Subgroup.card_le_of_le h
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective, first_card] at hc
  · have hc := Subgroup.card_le_of_le h
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, second_card] at hc
    omega

/-- A proper subgroup of odd index has index at least 1755. The Sylow
conjugation and both parabolic order bounds are discharged. -/
public theorem atlas1600_subgroup_index_ge_of_odd_index
    (L : Subgroup Atlas1600Group) (hL : L ≠ ⊤) (hodd : ¬ 2 ∣ L.index) :
    1755 ≤ L.index := by
  obtain ⟨g, hg⟩ := exists_conjugate_le_parabolic_of_odd_index L hL hodd
  have hc := atlas1600_subgroup_card_le_of_conjugate_parabolic L g hg
  by_contra h
  have hm := Nat.mul_le_mul hc (show L.index ≤ 1754 by omega)
  rw [L.card_mul_index, atlas1600Group_card] at hm
  norm_num at hm

end Tits
