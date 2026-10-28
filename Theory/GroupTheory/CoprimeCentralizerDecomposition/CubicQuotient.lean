module

public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Coprime decomposition through a quotient of order three

An element of order three supplements O₂(D) if D/O₂(D) has order three.
Consequently, if O₂(D) centralizes a normalized two-subgroup Z, the fixed
points of D on Z are those of that cyclic supplement. Coprime decomposition
then gives [Z,D]=Z when C_Z(D)=1.

Source application: Aschbacher--Smith, proof of 15.3.38, printed p.1136;
the action on the central two-kernel must be factored before using coprimality.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A cubic actor supplements the two-core when the quotient has order three. -/
theorem pCoreIn_sup_zpowers_eq_of_quotient_card_three {D : Subgroup G} {z : G}
    (hD : Nat.card (D ⧸ pCore 2 D) = 3) (hzD : z ∈ D) (hz3 : orderOf z = 3) :
    D.pCoreIn 2 ⊔ zpowers z = D := by
  let z' : D := ⟨z, hzD⟩
  let π := QuotientGroup.mk' (pCore 2 D)
  have hznot : π z' ≠ 1 := by
    intro hz
    have hzcore := (QuotientGroup.eq_one_iff _).mp hz
    have hc := (pCore_isPGroup (p := 2) (G := D)).orderOf_coprime
      (by decide : Nat.Coprime 2 3) (⟨z', hzcore⟩ : pCore 2 D)
    have ho : orderOf (⟨z', hzcore⟩ : pCore 2 D) = 3 := by
      simpa only [Subgroup.orderOf_mk, z'] using hz3
    rw [ho] at hc
    norm_num at hc
  have htop := zpowers_eq_top_of_prime_card hD hznot
  have hh := congrArg (Subgroup.comap π) htop
  rw [← MonoidHom.map_zpowers, comap_map_eq, QuotientGroup.ker_mk', comap_top] at hh
  have hm := congrArg (Subgroup.map D.subtype) hh
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype] at hm
  exact (sup_comm _ _).trans hm

/-- If the two-core acts trivially, a fixed-point-free action through a cubic
quotient moves the whole normalized two-subgroup. -/
theorem commutator_eq_of_twoCore_centralizes_of_quotient_card_three {D Z : Subgroup G}
    (hn : D ≤ normalizer (Z : Set G)) (hZ : IsPGroup 2 Z)
    (hcore : D.pCoreIn 2 ≤ centralizer (Z : Set G))
    (hD : Nat.card (D ⧸ pCore 2 D) = 3)
    (hfix : Z ⊓ centralizer (D : Set G) = ⊥)
    (hz : ∃ z ∈ D, orderOf z = 3) : ⁅Z, D⁆ = Z := by
  obtain ⟨z, hzD, hz3⟩ := hz
  have hgen := pCoreIn_sup_zpowers_eq_of_quotient_card_three hD hzD hz3
  have hZD : Z ≤ centralizer (D.pCoreIn 2 : Set G) := le_centralizer_iff.mp hcore
  have hzle : zpowers z ≤ D := zpowers_le.mpr hzD
  have hf : Z ⊓ centralizer (zpowers z : Set G) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    apply hfix.le
    refine ⟨hx.1, ?_⟩
    have hxc : zpowers x ≤ centralizer (D.pCoreIn 2 : Set G) :=
      zpowers_le.mpr (hZD hx.1)
    have hxz : zpowers x ≤ centralizer (zpowers z : Set G) := zpowers_le.mpr hx.2
    have hDx : D ≤ centralizer (zpowers x : Set G) := by
      rw [← hgen]
      exact sup_le (le_centralizer_iff.mp hxc) (le_centralizer_iff.mp hxz)
    exact le_centralizer_iff.mp hDx (mem_zpowers x)
  have hp3 : IsPGroup 3 (zpowers z) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hz3, pow_one])
  have hcop : Nat.Coprime (Nat.card (zpowers z)) (Nat.card Z) :=
    IsPGroup.coprime_card_of_ne 3 2 (by decide) (zpowers z) Z hp3 hZ
  let : Group.IsNilpotent Z := hZ.isNilpotent
  have hm := eq_commutator_sup_centralizer_of_solvable_coprime Z (zpowers z)
    (hzle.trans hn) inferInstance hcop
  rw [hf, sup_bot_eq] at hm
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp hn)
  exact hm.le.trans (commutator_mono le_rfl hzle)
end Subgroup
