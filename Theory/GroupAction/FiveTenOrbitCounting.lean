module
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Set.Card

/-!
# Five-and-ten orbit counting

A group of order twenty acts by automorphisms on a group of order sixteen.
Suppose every nonidentity orbit has size divisible by five, and a subgroup
of order four fixes at most two elements. Then the nonidentity orbits have
sizes five and ten. The four-group has exactly one nonidentity fixed point;
every five-element orbit contains that point, so there is only one such orbit.

This is the orbit-counting part of the calculation in D. Parrott,
*A characterization of the Tits' simple group* (1972), pp.673–674.
-/

namespace Theory.GroupAction
open MulAction

/-- A four-subgroup with only two fixed points forces the five-and-ten census. -/
public theorem five_ten_orbit_census_of_fixed_card_le_two
    {M P V : Type*} [Group M] [Finite M] [Group P] [Finite P]
    [Group V] [Finite V] [MulDistribMulAction M V]
    (hM : Nat.card M = 20) (hP : Nat.card P = 4) (hV : Nat.card V = 16)
    (i : P →* M) (hi : Function.Injective i)
    (hdiv : ∀ v : V, v ≠ 1 → 5 ∣ (orbit M v).ncard)
    (hfixed : letI := MulDistribMulAction.compHom V i
      Nat.card (FixedPoints.subgroup P V) ≤ 2) :
    ∃ x y : V, x ≠ 1 ∧ y ≠ 1 ∧ (orbit M x).ncard = 5 ∧
      (orbit M y).ncard = 10 ∧ ∀ w : V, w ≠ 1 → w ∈ orbit M x ∪ orbit M y := by
  classical
  let : MulDistribMulAction P V := MulDistribMulAction.compHom V i
  let F := FixedPoints.subgroup P V
  have hp : IsPGroup 2 P := IsPGroup.of_card (n := 2) hP
  have hmod := hp.card_modEq_card_fixedPoints V
  change Nat.ModEq 2 (Nat.card V) (Nat.card F) at hmod
  have hpos : 0 < Nat.card F := Nat.card_pos
  have hF : Nat.card F = 2 := by
    change Nat.card F ≤ 2 at hfixed
    rw [hV] at hmod
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨x, hx, huniq⟩ := (Nat.card_eq_two_iff' (1 : F)).mp hF
  have hx1 : (x : V) ≠ 1 := fun h => hx (Subtype.ext h)
  have hsub (v : V) (hv : v ≠ 1) : orbit M v ⊆ ({1} : Set V)ᶜ := by
    rintro w ⟨g, rfl⟩ heq
    apply hv
    have hh := congrArg (fun z : V => g⁻¹ • z) heq
    simpa only [inv_smul_smul, smul_one] using hh
  have hcompl : (({1} : Set V)ᶜ).ncard = 15 := by
    rw [Set.ncard_compl, hV, Set.ncard_singleton]
  have hcount (v : V) :
      (orbit M v).ncard * Nat.card (stabilizer M v) = 20 := by
    change Nat.card (orbit M v) * Nat.card (stabilizer M v) = 20
    rw [← hM, ← Nat.card_prod]
    exact Nat.card_congr (orbitProdStabilizerEquivGroup M v)
  have hcases (v : V) (hv : v ≠ 1) :
      (orbit M v).ncard = 5 ∨ (orbit M v).ncard = 10 := by
    have hle : (orbit M v).ncard ≤ 15 := (Set.ncard_le_ncard (hsub v hv)).trans_eq hcompl
    have hpos : 0 < (orbit M v).ncard := (Set.ncard_pos (Set.toFinite _)).mpr
      ⟨v, mem_orbit_self v⟩
    have hd := hdiv v hv
    have hd20 : (orbit M v).ncard ∣ 20 := ⟨_, (hcount v).symm⟩
    have hor : (orbit M v).ncard = 5 ∨ (orbit M v).ncard = 10 ∨
        (orbit M v).ncard = 15 := by omega
    rcases hor with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · norm_num [h] at hd20
  have hx5 : (orbit M (x : V)).ncard = 5 := by
    let j : P → stabilizer M (x : V) := fun p => ⟨i p, x.property p⟩
    have hj : Function.Injective j := fun p q h => hi (congrArg Subtype.val h)
    have hstab : 4 ≤ Nat.card (stabilizer M (x : V)) := by
      simpa only [hP] using Nat.card_le_card_of_injective j hj
    have hc := hcount (x : V)
    rcases hcases (x : V) hx1 with h | h
    · exact h
    · rw [h] at hc
      omega
  have hsame (v : V) (hv : v ≠ 1) (h5 : (orbit M v).ncard = 5) :
      orbit M v = orbit M (x : V) := by
    let : MulAction P (orbit M v) := MulAction.compHom (orbit M v) i
    have hm := hp.card_modEq_card_fixedPoints (orbit M v)
    have hne : (fixedPoints P (orbit M v)).Nonempty := by
      by_contra hn
      have he : fixedPoints P (orbit M v) = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
      have hz : Nat.card (fixedPoints P (orbit M v)) = 0 := by
        rw [he]
        exact Nat.card_of_isEmpty
      change Nat.ModEq 2 ((orbit M v).ncard) _ at hm
      norm_num [h5, hz, Nat.ModEq] at hm
    obtain ⟨z, hz⟩ := hne
    have hzF : (z : V) ∈ F := fun p => congrArg Subtype.val (hz p)
    have hz1 : (z : V) ≠ 1 := hsub v hv z.property
    have hzx : (z : V) = x := congrArg Subtype.val
      (huniq ⟨z, hzF⟩ (fun hh => hz1 (congrArg Subtype.val hh)))
    have hxO : (x : V) ∈ orbit M v := hzx ▸ z.property
    exact (orbit_eq_iff.mpr hxO).symm
  have hex : ∃ y : V, y ≠ 1 ∧ y ∉ orbit M (x : V) := by
    by_contra hn
    have hs : ({1} : Set V)ᶜ ⊆ orbit M (x : V) := by
      intro y hy
      by_contra hny
      exact hn ⟨y, hy, hny⟩
    have hh := Set.ncard_le_ncard hs
    rw [hcompl, hx5] at hh
    omega
  obtain ⟨y, hy, hyx⟩ := hex
  have hy10 : (orbit M y).ncard = 10 := by
    rcases hcases y hy with h | h
    · exact (hyx ((hsame y hy h) ▸ mem_orbit_self (M := M) y)).elim
    · exact h
  have hdisj : Disjoint (orbit M (x : V)) (orbit M y) := by
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    have he := (orbit_eq_iff.mpr hzy).symm.trans (orbit_eq_iff.mpr hzx)
    exact hyx (he ▸ mem_orbit_self y)
  have heq : orbit M (x : V) ∪ orbit M y = ({1} : Set V)ᶜ := by
    apply Set.eq_of_subset_of_ncard_le (Set.union_subset (hsub _ hx1) (hsub _ hy))
    rw [Set.ncard_union_eq hdisj, hx5, hy10, hcompl]
  exact ⟨x, y, hx1, hy, hx5, hy10, fun w hw => heq.symm ▸ hw⟩

end Theory.GroupAction
