module

public import Stellmacher.Recognition.OddCoreComponentNormalizer
public import Theory.GroupTheory.ElementaryCommutingOddQuotient

/-!
# Odd-quotient control of completed odd-core closures

An overgroup of an elementary binary actor of rank at least three normalizes
its completed odd-core closure if an odd normal quotient has either a normal
four-group or a normal two-subgroup of rank at least three. Lift the actor to
the overgroup, apply the actual commuting-component transport theorem, and
map the path back to the ambient group. Consequently failure of control bounds
the elementary rank of every normal two-subgroup of that quotient by two.

These lemmas are shared by involution-centralizer analysis and minimal-simple
maximal-overgroup analysis. Source: GLS2, Chapter F, Sections 21–22, together
with the coprime and Frattini arguments in ElementaryCommutingOddQuotient.
-/

namespace Stellmacher.Recognition

/-- A normal four-group modulo an odd normal subgroup controls the closure
of every rank-three elementary actor in the overgroup. -/
public theorem le_oddCoreClosure_normalizer_of_normal_four_odd_quotient
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (A H : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) (hAH : A ≤ H)
    (N : Subgroup H) [N.Normal] (hNodd : Odd (Nat.card N))
    (U : Subgroup (H ⧸ N)) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 4) :
    H ≤ Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  let AH := A.subgroupOf H
  let : IsElementaryAbelian 2 AH := IsElementaryAbelian.subgroupOf hAH
  have hAH8 : 8 ≤ Nat.card AH := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv]
  intro g hg
  let gH : H := ⟨g, hg⟩
  have hpath := Subgroup.elementaryCommutingConnected_conj_of_normal_four_odd_quotient
    N AH hNodd hAH8 U hU gH
  have hm : (AH.map (MulAut.conj gH).toMonoidHom).map H.subtype =
      A.map (MulAut.conj g).toMonoidHom := by
    calc
      _ = (AH.map H.subtype).map (MulAut.conj g).toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        rfl
      _ = _ := by rw [Subgroup.map_subgroupOf_eq_of_le hAH]
  have hpathG := hpath.map_injective H.subtype H.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hAH, hm] at hpathG
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change (involutionOddCoreClosure A).map (MulAut.conj g).toMonoidHom = _
  rw [involutionOddCoreClosure_map]
  exact (oddCoreClosure_eq_of_connected hN hpathG).symm

/-- A normal two-subgroup containing an elementary eight modulo an odd
normal subgroup controls the closure of every rank-three actor in the overgroup. -/
public theorem le_oddCoreClosure_normalizer_of_normal_rank_three_odd_quotient
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (A H : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) (hAH : A ≤ H)
    (N : Subgroup H) [N.Normal] (hNodd : Odd (Nat.card N))
    (Q D : Subgroup (H ⧸ N)) [Q.Normal] (hQ : IsPGroup 2 Q)
    [IsElementaryAbelian 2 D] (hD : 8 ≤ Nat.card D) (hDQ : D ≤ Q) :
    H ≤ Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  let AH := A.subgroupOf H
  let : IsElementaryAbelian 2 AH := IsElementaryAbelian.subgroupOf hAH
  have hAH8 : 8 ≤ Nat.card AH := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv]
  intro g hg
  let gH : H := ⟨g, hg⟩
  have hpath := Subgroup.elementaryCommutingConnected_conj_of_normal_odd_quotient
    N AH hNodd hAH8 Q D hQ hD hDQ gH
  have hm : (AH.map (MulAut.conj gH).toMonoidHom).map H.subtype =
      A.map (MulAut.conj g).toMonoidHom := by
    calc
      _ = (AH.map H.subtype).map (MulAut.conj g).toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        rfl
      _ = _ := by rw [Subgroup.map_subgroupOf_eq_of_le hAH]
  have hpathG := hpath.map_injective H.subtype H.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hAH, hm] at hpathG
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change (involutionOddCoreClosure A).map (MulAut.conj g).toMonoidHom = _
  rw [involutionOddCoreClosure_map]
  exact (oddCoreClosure_eq_of_connected hN hpathG).symm

/-- If an overgroup fails to control the closure, its odd quotient's
normal two-subgroups contain no elementary eight. In particular this applies
to the two-core; it does not assert a structural dichotomy for that quotient. -/
public theorem card_lt_eight_of_not_le_oddCoreClosure_normalizer
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (A H : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) (hAH : A ≤ H)
    (N : Subgroup H) [N.Normal] (hNodd : Odd (Nat.card N))
    (hnot : ¬ H ≤ Subgroup.normalizer (involutionOddCoreClosure A : Set G))
    (Q D : Subgroup (H ⧸ N)) [Q.Normal] (hQ : IsPGroup 2 Q)
    [IsElementaryAbelian 2 D] (hDQ : D ≤ Q) : Nat.card D < 8 := by
  by_contra! hD
  exact hnot (le_oddCoreClosure_normalizer_of_normal_rank_three_odd_quotient
    hN A H hA hAH N hNodd Q D hQ hD hDQ)

end Stellmacher.Recognition
