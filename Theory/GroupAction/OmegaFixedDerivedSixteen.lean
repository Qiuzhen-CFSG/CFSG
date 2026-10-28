module

public import Theory.GroupTheory.PGroup.Omega
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.Lemmas
public import Theory.GroupTheory.NormalizedSupCard
import Mathlib.GroupTheory.Nilpotent

/-!
# Cubic fixed points in the derived subgroup

For a group K of order 1024, with derived subgroup of order 64 and first
2-omega subgroup U of order 256, a cubic action whose fixed points lie in U
has its fixed points in K′, provided some square lies outside K′.

The index-four quotient K/U is abelian. In the order-sixteen abelianization,
the image B of U has order four and exponent two. Coprime fixed-point lifting
places the fixed subgroup in B, and orbit counting gives its order as one or
four. In the latter case the fixed/displacement decomposition has two factors
of order four. The moving factor is fixed-point-free, so orbit counting on its
nontrivial characteristic omega subgroup makes it elementary abelian too.
This would make the entire abelianization have exponent two, a contradiction.
Only the image of U is asserted to be elementary abelian.

Source: the fixed-point deduction in Parrott, *A characterization of the Tits'
simple group* (1972), p.677. The argument here isolates the numerical and action
hypotheses and uses the coprime-action results in `Theory.GroupAction.CoprimeHall`.
-/

open scoped IsMulCommutative

namespace Theory.GroupAction

private theorem card_fixed_mod_three
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G]
    [MulDistribMulAction A G] (hA : Nat.card A = 3) :
    Nat.card G % 3 = Nat.card (FixedPoints.subgroup A G) % 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  exact hp.card_modEq_card_fixedPoints G

private theorem pow_two_eq_one_of_card_four_fixed_bot
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G]
    [MulDistribMulAction A G] (hA : Nat.card A = 3) (hG : Nat.card G = 4)
    (hfix : FixedPoints.subgroup A G = ⊥) : ∀ x : G, x ^ 2 = 1 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsMulCommutative G := IsPGroup.isMulCommutative_of_card_eq_prime_sq
    (p := 2) (by simpa using hG)
  let U := omega₁ G (p := 2)
  let : U.Characteristic := omega₁_characteristic G
  let : IsInvariant A G U := isInvariant_of_characteristic U
  have hfixU : FixedPoints.subgroup A U = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hxG : (x : G) ∈ FixedPoints.subgroup A G := by
      intro a
      exact congrArg Subtype.val (hx a)
    have hxone : (x : G) = 1 := by simpa [hfix] using hxG
    exact Subtype.ext hxone
  have hmod := card_fixed_mod_three (G := U) hA
  rw [hfixU, Subgroup.card_bot] at hmod
  have hle : Nat.card U ≤ 4 := by
    simpa [hG] using (Nat.card_le_card_of_injective U.subtype Subtype.val_injective)
  have hne : U ≠ ⊥ := by
    classical
    let : Fintype G := Fintype.ofFinite G
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := G) 2
      (by simp [← Nat.card_eq_fintype_card, hG])
    have hmem : x ∈ U := Subgroup.subset_closure (by
      simpa [hx] using pow_orderOf_eq_one x)
    intro hbot
    have hxone : x = 1 := by simpa [hbot] using hmem
    simp [hxone] at hx
  have hpos : 0 < Nat.card U := Nat.card_pos
  have hnotone : Nat.card U ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  have hcard : Nat.card U = 4 := by omega
  have htop : U = ⊤ := (Subgroup.card_eq_iff_eq_top U).mp (hcard.trans hG.symm)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.omega₁_of_isMulCommutative G
  intro x
  exact elemPow_eq_one_of_isElementaryAbelian x (show x ∈ U by rw [htop]; trivial)

private theorem fixed_bot_of_card_sixteen
    {A V : Type*} [Group A] [Finite A] [CommGroup V] [Finite V]
    [MulDistribMulAction A V] (hA : Nat.card A = 3) (hV : Nat.card V = 16)
    (B : Subgroup V) (hB : Nat.card B = 4) (hBpow : ∀ x ∈ B, x ^ 2 = 1)
    (hfix : FixedPoints.subgroup A V ≤ B) (hsquare : ∃ x : V, x ^ 2 ≠ 1) :
    FixedPoints.subgroup A V = ⊥ := by
  let F := FixedPoints.subgroup A V
  let D := commutatorAction A V
  have hmod := card_fixed_mod_three (G := V) hA
  have hle : Nat.card F ≤ 4 := hB ▸ Subgroup.card_le_of_le hfix
  have hpos : 0 < Nat.card F := Nat.card_pos
  change Nat.card V % 3 = Nat.card F % 3 at hmod
  rw [hV] at hmod
  have hcases : Nat.card F = 1 ∨ Nat.card F = 4 := by omega
  rcases hcases with hone | hfour
  · exact Subgroup.card_eq_one.mp hone
  have hFB : F = B := Subgroup.eq_of_le_of_card_ge hfix (by omega)
  have hcompl : IsCompl F D :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (A := A) (G := V) inferInstance (by rw [hA, hV]; decide) inferInstance
  have hcount := Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint F D
    (by rw [Subgroup.normalizer_eq_top]; exact le_top) hcompl.disjoint
  rw [hcompl.sup_eq_top, Subgroup.card_top, hV, hfour] at hcount
  have hD : Nat.card D = 4 := by omega
  let : IsInvariant A V D := commutatorAction_normal_and_invariant.2
  have hDfix : FixedPoints.subgroup A D = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hxF : (x : V) ∈ F := fun a => congrArg Subtype.val (hx a)
    have hxone : (x : V) = 1 := by
      have hxinf : (x : V) ∈ F ⊓ D := ⟨hxF, x.property⟩
      simpa [hcompl.inf_eq_bot] using hxinf
    exact Subtype.ext hxone
  have hDpow := pow_two_eq_one_of_card_four_fixed_bot hA hD hDfix
  obtain ⟨x, hx⟩ := hsquare
  have hxsup : x ∈ F ⊔ D := by rw [hcompl.sup_eq_top]; trivial
  obtain ⟨f, hf, d, hd, rfl⟩ := Subgroup.mem_sup.mp hxsup
  exfalso
  apply hx
  have hf2 : f ^ 2 = 1 := hBpow f (hFB ▸ hf)
  have hd2 : d ^ 2 = 1 := congrArg Subtype.val (hDpow ⟨d, hd⟩)
  simp [mul_pow, hf2, hd2]

/-- A cubic action on a group with orders `|K| = 1024`, `|K′| = 64`, and
`|Ω₁(K)| = 256` has its fixed points in `K′` if they lie in `Ω₁(K)` and
some square is outside `K′`. The given action is retained throughout. -/
public theorem fixedPoints_le_commutator_of_card_omega
    {A K : Type*} [Group A] [Finite A] [Group K] [Finite K]
    [MulDistribMulAction A K]
    (hA : Nat.card A = 3) (hK : Nat.card K = 1024)
    (hderived : Nat.card (commutator K) = 64)
    (homega : Nat.card (omega₁ K (p := 2)) = 256)
    (hsquare : ∃ k : K, k ^ 2 ∉ commutator K)
    (hfixed : FixedPoints.subgroup A K ≤ omega₁ K (p := 2)) :
    FixedPoints.subgroup A K ≤ commutator K := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U := omega₁ K (p := 2)
  let : U.Characteristic := omega₁_characteristic K
  have hUcard : Nat.card U = 256 := homega
  have hQU : Nat.card (K ⧸ U) = 4 := by
    have hc := U.card_mul_index
    rw [Subgroup.index_eq_card, hUcard, hK] at hc
    omega
  have hUcomm : IsMulCommutative (K ⧸ U) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hQU)
  have hDU : commutator K ≤ U :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hUcomm
  let V := K ⧸ commutator K
  let : IsMulCommutative V :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  let : CommGroup V := inferInstance
  let hInv : IsInvariant A K (commutator K) := isInvariant_of_characteristic _
  let : MulDistribMulAction A V := quotientMulDistribMulAction (commutator K) hInv
  let q : K →* V := QuotientGroup.mk' (commutator K)
  let B := U.map q
  have hV : Nat.card V = 16 := by
    have hc := (commutator K).card_mul_index
    rw [Subgroup.index_eq_card, hderived, hK] at hc
    change 64 * Nat.card V = 1024 at hc
    omega
  have hB : Nat.card B = 4 := by
    have hc := ((commutator K).subgroupOf U).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDU).toEquiv,
      hderived, Subgroup.index_eq_card, hUcard] at hc
    have hBquot : Nat.card B = Nat.card (U ⧸ (commutator K).subgroupOf U) :=
      natCard_map_mk'_eq U (commutator K)
    omega
  have hBpow : ∀ x ∈ B, x ^ 2 = 1 := by
    rintro x ⟨u, hu, rfl⟩
    apply Subgroup.closure_induction (p := fun z _ => (q z) ^ 2 = 1) _ _ _ _ hu
    · intro z hz
      have hz2 : z ^ 2 = 1 := by simpa using hz
      simpa only [map_pow, map_one] using congrArg q hz2
    · simp
    · intro z w _ _ hz hw
      simp only [map_mul, mul_pow, hz, hw, one_mul]
    · intro z _ hz
      simp [hz]
  have hKp : IsPGroup 2 K := IsPGroup.of_card (n := 10) (by simpa using hK)
  let : Group.IsNilpotent K := hKp.isNilpotent
  have hcop : Nat.Coprime (Nat.card A) (Nat.card K) := by rw [hA, hK]; decide
  have hfixV : FixedPoints.subgroup A V = (FixedPoints.subgroup A K).map q :=
    fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime inferInstance hcop
      (commutator K) hInv
  have hfixB : FixedPoints.subgroup A V ≤ B := by
    rw [hfixV]
    exact Subgroup.map_mono hfixed
  have hsquareV : ∃ x : V, x ^ 2 ≠ 1 := by
    obtain ⟨k, hk⟩ := hsquare
    refine ⟨q k, ?_⟩
    intro heq
    apply hk
    apply (QuotientGroup.eq_one_iff _).mp
    change q (k ^ 2) = 1
    simpa only [map_pow] using heq
  have hbot := fixed_bot_of_card_sixteen hA hV B hB hBpow hfixB hsquareV
  intro k hk
  apply (QuotientGroup.eq_one_iff k).mp
  change q k = 1
  have hmem : q k ∈ FixedPoints.subgroup A V := by
    rw [hfixV]
    exact Subgroup.mem_map_of_mem q hk
  simpa [hbot] using hmem

end Theory.GroupAction
