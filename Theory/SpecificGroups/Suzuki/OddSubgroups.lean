module

public import Theory.SpecificGroups.Suzuki.MaximalNonsplitTori
public import Mathlib.GroupTheory.SpecificGroups.ZGroup

/-!
# Odd-order subgroups of Suzuki groups

Every odd-prime Sylow subgroup is cyclic. For primes dividing the ovoid
degree this follows from the nonsplit linear theorem. Otherwise the Sylow
subgroup fixes a point; its action on the complement fixes a second point,
since that complement has 2-power cardinality. The two-point stabilizer is
a conjugate of the cyclic split torus.

Consequently odd-order subgroups are Z-groups and hence solvable. This gives
the existence of involutions needed in the nonsolvable subgroup analysis of
Huppert--Blackburn, *Finite Groups III*, XI.3.12(e), without the odd-order
theorem or a subgroup classification.
-/

namespace BenderSuzuki.MatrixGroups

/-- A subgroup fixing two distinct ovoid points is cyclic. -/
public theorem suzukiSubgroup_isCyclic_of_fix_pair {m : ℕ} (hm : 0 < m)
    (H : Subgroup (SuzukiMatrixGroup m)) (a b : SuzukiOvoid m) (hab : a ≠ b)
    (ha : ∀ g : H, (g : SuzukiMatrixGroup m) • a = a)
    (hb : ∀ g : H, (g : SuzukiMatrixGroup m) • b = b) : IsCyclic H := by
  obtain ⟨k, hka, hkb⟩ := MulAction.is_two_pretransitive_iff.mp
    (suzukiOvoid_two_pretransitive m) hab (suzukiOvoidInfinity_ne_zero m)
  let f : H →* SuzukiSplitTorus m :=
    { toFun := fun g => ⟨MulAut.conj k g.val, by
        rw [mem_suzukiSplitTorus_iff_fix_pair]
        constructor
        · rw [← hka]
          change (k * g.val * k⁻¹) • (k • a) = k • a
          simp only [mul_smul, inv_smul_smul, ha]
        · rw [← hkb]
          change (k * g.val * k⁻¹) • (k • b) = k • b
          simp only [mul_smul, inv_smul_smul, hb]⟩
      map_one' := Subtype.ext (map_one (MulAut.conj k))
      map_mul' := fun g h => Subtype.ext (map_mul (MulAut.conj k) g.val h.val) }
  let := suzukiSplitTorus_isCyclic m hm
  apply isCyclic_of_injective f
  intro g h heq
  exact Subtype.ext ((MulAut.conj k).injective (congrArg Subtype.val heq))

/-- All Sylow subgroups for odd primes are cyclic. -/
public theorem suzukiSylow_isCyclic_of_ne_two {m : ℕ} (hm : 0 < m)
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (P : Sylow p (SuzukiMatrixGroup m)) : IsCyclic P := by
  classical
  by_cases hpd : p ∣ (2 ^ (2 * m + 1)) ^ 2 + 1
  · exact suzukiMatrixGroup_isCyclic_of_card_dvd_sq_add_one m hm P
      (suzukiSylow_card_dvd_degree m hm hpd P)
  have hPfix : ∃ a : SuzukiOvoid m, ∀ t : P, (t : SuzukiMatrixGroup m) • a = a := by
    obtain ⟨a, ha⟩ := P.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card
      (SuzukiOvoid m) (by rwa [suzukiOvoid_card])
    exact ⟨a, MulAction.mem_fixedPoints.mp ha⟩
  obtain ⟨a, ha⟩ := hPfix
  let X : SubMulAction P (SuzukiOvoid m) :=
    { carrier := {b | b ≠ a}
      smul_mem' := by
        intro g b hb h
        apply hb
        have h' := congrArg (fun z => (g⁻¹ : P) • z) h
        rw [inv_smul_smul] at h'
        exact h'.trans (ha g⁻¹) }
  have hcard : Nat.card X = (2 ^ (2 * m + 1)) ^ 2 := by
    let := Fintype.ofFinite (SuzukiOvoid m)
    change Nat.card {b : SuzukiOvoid m // ¬ b = a} = _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp only [Fintype.card_unique, ← Nat.card_eq_fintype_card, suzukiOvoid_card,
      Nat.add_sub_cancel]
  have hpn : ¬ p ∣ Nat.card X := by
    rw [hcard]
    intro h
    exact hp2 (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two |>.mp
      (hp.out.dvd_of_dvd_pow (hp.out.dvd_of_dvd_pow h)))
  obtain ⟨b, hb⟩ := P.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card X hpn
  exact suzukiSubgroup_isCyclic_of_fix_pair hm P a b.val (Ne.symm b.property) ha
    (fun g => congrArg Subtype.val (MulAction.mem_fixedPoints.mp hb g))

/-- An odd-order Suzuki subgroup is a Z-group. -/
public theorem suzukiSubgroup_isZGroup_of_odd {m : ℕ} (hm : 0 < m)
    (H : Subgroup (SuzukiMatrixGroup m)) (hodd : Odd (Nat.card H)) : IsZGroup H := by
  constructor
  intro p hp P
  let : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst p
    have hPcard : Nat.card P = 1 := by
      obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
      by_cases hn0 : n = 0
      · simpa only [hn0, pow_zero] using hn
      · exact False.elim (hodd.not_two_dvd_nat
          ((hn ▸ dvd_pow_self 2 hn0).trans (P : Subgroup H).card_subgroup_dvd_card))
    have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hPcard).1
    exact inferInstance
  · obtain ⟨Q, hQ⟩ := P.exists_comap_subtype_eq
    let := suzukiSylow_isCyclic_of_ne_two hm hp2 Q
    let f : P →* Q :=
      { toFun := fun g => ⟨g.val.val, by
          change g.val ∈ (Q : Subgroup (SuzukiMatrixGroup m)).comap H.subtype
          rw [hQ]
          exact g.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    apply isCyclic_of_injective f
    intro x y h
    exact Subtype.ext (Subtype.ext
      (congrArg (fun z : Q => (z : SuzukiMatrixGroup m)) h))

/-- Odd-order subgroups are solvable by the finite Z-group theorem. -/
public theorem suzukiSubgroup_isSolvable_of_odd {m : ℕ} (hm : 0 < m)
    (H : Subgroup (SuzukiMatrixGroup m)) (hodd : Odd (Nat.card H)) :
    Group.IsSolvable H := by
  let := suzukiSubgroup_isZGroup_of_odd hm H hodd
  infer_instance

/-- A nonsolvable Suzuki subgroup contains an involution. -/
public theorem suzukiSubgroup_exists_involution {m : ℕ} (hm : 0 < m)
    (H : Subgroup (SuzukiMatrixGroup m)) (hH : ¬ Group.IsSolvable H) :
    ∃ t : H, orderOf t = 2 := by
  apply exists_prime_orderOf_dvd_card' 2
  by_contra h
  exact hH (suzukiSubgroup_isSolvable_of_odd hm H
    (Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using h)))

end BenderSuzuki.MatrixGroups
