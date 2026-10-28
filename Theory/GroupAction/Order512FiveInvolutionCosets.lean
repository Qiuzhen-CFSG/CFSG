module

public import Theory.GroupAction.Order512FiveOrbit
public import Theory.GroupTheory.FrattiniInvolutionCosets
public import Theory.Frattini.PGroup

/-!
# The five involutory cosets in the order-512 residual

For the intrinsic class-three two-group of order 512 with an order-five
actor fixing only central elements, all nonidentity derived cosets with
involutory lifts form one five-element orbit. Coprime fixed-point lifting
makes the action on the Frattini quotient fixed-point-free. Each nonzero
orbit has five points, while the Frattini involution obstruction bounds the
whole involutory set by nine. Thus two such orbits cannot be disjoint.

Source: Thompson VI, printed p.630, the involutory residual cosets;
Parrott, A characterization of the Tits' simple group (1972), Lemma 4.
-/

namespace Theory.GroupAction
open Subgroup MulAction
open scoped IsMulCommutative

private theorem prime_orbit_card_five
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V] (hA : Nat.card A = 5)
    (hfixed : FixedPoints.subgroup A V = ⊥) (x : V) (hx : x ≠ 1) :
    (orbit A x).ncard = 5 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hinj : Function.Injective (fun a : A => a • x) := by
    intro a b hab
    change a • x = b • x at hab
    by_contra hne
    have hn : a⁻¹ * b ≠ 1 := by
      intro hh
      exact hne (inv_mul_eq_one.mp hh)
    have hstab : stabilizer A x = ⊤ := by
      apply top_unique
      rw [← zpowers_eq_top_of_prime_card hA hn]
      apply zpowers_le.mpr
      change (a⁻¹ * b) • x = x
      rw [mul_smul, ← hab, inv_smul_smul]
    have hfix : x ∈ FixedPoints.subgroup A V := by
      intro c
      exact show c ∈ stabilizer A x from hstab ▸ mem_top c
    exact hx (mem_bot.mp (hfixed ▸ hfix))
  exact (Set.ncard_range_of_injective hinj).trans hA

/-- Every involutory nonidentity derived coset lies in the orbit of any
specified such coset, and there are precisely five such cosets. -/
public theorem parrott_involutory_derived_coset_census
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V]
    (hV : IsPGroup 2 V) (hcard : Nat.card V = 512)
    (hclass : 3 ≤ Group.nilpotencyClass V) (hA : Nat.card A = 5)
    (hfixed : FixedPoints.subgroup A V ≤ center V)
    (b : V) (hb : b ^ 2 = 1) (hbD : b ∉ commutator V) :
    let D := commutator V
    let q := QuotientGroup.mk' D
    let T := {x : V ⧸ D | x ≠ 1 ∧ ∃ a : V, a ^ 2 = 1 ∧ q a = x}
    T.ncard = 5 ∧
      ∀ x : V, x ^ 2 = 1 → x ∉ D → ∃ a : A, q (a • x) = q b := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (IsPGroup 2 V) := ⟨hV⟩
  let _ : Group.IsNilpotent V := hV.isNilpotent
  obtain ⟨_, _, hPhi, hUpper, hD, hDcard⟩ :=
    parrott_twoGroup_structure hV hcard hclass hA hfixed
  let D := commutator V
  let q := QuotientGroup.mk' D
  let _ : IsElementaryAbelian 2 D := hD
  let _ : IsElementaryAbelian 2 (V ⧸ D) := by
    change IsElementaryAbelian 2 (V ⧸ commutator V)
    let _ := isElementaryAbelian_quotient_frattini (R := V) (p := 2)
    let e := QuotientGroup.quotientMulEquivOfEq hPhi
    refine { is_comm := ⟨fun x y => e.injective ?_⟩, exponent_dvd_p := ?_ }
    · simpa only [map_mul] using (mul_comm (e x) (e y))
    · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply e.injective
      simpa only [map_pow, map_one] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (V ⧸ frattini V)) (e x))
  let _ : MulDistribMulAction A (V ⧸ D) :=
    quotientMulDistribMulAction D (isInvariant_of_characteristic D)
  have hquot : Nat.card (V ⧸ D) = 16 := by
    have hh := D.index_mul_card
    change Nat.card (V ⧸ D) * Nat.card D = Nat.card V at hh
    rw [hDcard, hcard] at hh
    omega
  have hZ : center V ≤ D := by
    change center V ≤ commutator V
    rw [hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using
      Subgroup.upperCentralSeries_mono V (show 1 ≤ 2 by decide)
  have hfix : FixedPoints.subgroup A (V ⧸ D) = ⊥ := by
    rw [fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime
      (inferInstance : Group.IsSolvable V) (by rw [hA, hcard]; decide)
      D (isInvariant_of_characteristic D), Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
    exact hfixed.trans hZ
  let T : Set (V ⧸ D) := {x | x ≠ 1 ∧ ∃ a : V, a ^ 2 = 1 ∧ q a = x}
  have hsmall : T.ncard < 10 :=
    nonidentity_involutory_cosets_ncard_lt_ten D hPhi hUpper hquot
  have hne (x : V) (hx : x ∉ D) : q x ≠ 1 :=
    fun hh => hx ((QuotientGroup.eq_one_iff x).mp hh)
  have hOT (x : V) (hx : x ^ 2 = 1) (hxD : x ∉ D) : orbit A (q x) ⊆ T := by
    rintro w ⟨a, rfl⟩
    refine ⟨?_, a • x, ?_, ?_⟩
    · intro hh
      exact hne x hxD (smul_left_cancel a (hh.trans (smul_one a).symm))
    · exact (map_pow (MulDistribMulAction.toMulAut A V a) x 2).symm.trans
        (by rw [hx, map_one])
    · rfl
  have hOcard (x : V) (hxD : x ∉ D) : (orbit A (q x)).ncard = 5 :=
    prime_orbit_card_five hA hfix (q x) (hne x hxD)
  have hmem (x : V) (hx : x ^ 2 = 1) (hxD : x ∉ D) : q b ∈ orbit A (q x) := by
    by_contra hn
    have hdis : Disjoint (orbit A (q x)) (orbit A (q b)) := by
      apply Set.disjoint_left.mpr
      intro w hwx hwb
      have heq := (orbit_eq_iff.mpr hwx).symm.trans (orbit_eq_iff.mpr hwb)
      apply hn
      rw [heq]
      exact mem_orbit_self _
    have hbound := Set.ncard_le_ncard (Set.union_subset (hOT x hx hxD) (hOT b hb hbD))
    rw [Set.ncard_union_eq hdis, hOcard x hxD, hOcard b hbD] at hbound
    omega
  have heq : T = orbit A (q b) := by
    apply Set.Subset.antisymm ?_ (hOT b hb hbD)
    rintro w ⟨hw, x, hx, rfl⟩
    have hxD : x ∉ D := fun hh => hw ((QuotientGroup.eq_one_iff x).mpr hh)
    rw [orbit_eq_iff.mpr (hmem x hx hxD)]
    exact mem_orbit_self _
  change T.ncard = 5 ∧ _
  refine ⟨heq.symm ▸ hOcard b hbD, ?_⟩
  intro x hx hxD
  obtain ⟨a, ha⟩ := hmem x hx hxD
  exact ⟨a, ha⟩

end Theory.GroupAction
