module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeExclusion.Preparation
public import Theory.GroupTheory.SylowCenterDivisor
public import Theory.GroupTheory.CyclicSylowNormalComplement
public import Theory.GroupTheory.NoNormalFourNormalComplement
public import Theory.GroupTheory.NormalFourThreeDivisor

/-!
# The Sylow-center argument in prime binary degree

The order formula excludes the prime three. Primitivity at even degree and
the trivial two-core exclude a normal two-complement, and Burnside transfer
therefore excludes cyclic Sylow two-subgroups. If the Sylow center were
cyclic, the absence of a normal four would give a normal two-complement;
the presence of a normal four would make three divide its ambient normalizer
by Thompson's argument. Thus the center is noncyclic. Burnside fusion on
the actual Ω₁(Z(S)) then yields (3G) with its precise rank bound r ≤ n.

The final theorem discharges both local group-theoretic inputs. The single
ambient conjugacy class of involutions remains an explicit independent input,
as supplied by the first assertion of Lemma 3.10.

Source: GLS, Volume 4, Chapter 1, Lemma 3.10 and (3G),
`refs/KGroup/GLS4/Chapter1.tex`, lines 450–462.
-/

open Subgroup MulAction
namespace MulAction.SemilinearPointStabilizer.PrimeExclusion

/-- In odd prime binary degree greater than three the ambient order is prime to three. -/
public theorem three_not_dvd_card {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
    [MulAction X F] [FaithfulSMul X F]
    (c : Coordinates X F) [IsPretransitive X F]
    {n : ℕ} (hn : n.Prime) (hodd : Odd n) (hn3 : 3 < n)
    (hF : Nat.card F = 2 ^ n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n) : ¬ 3 ∣ Nat.card X := by
  have hnmod : 2 ^ n % 3 = 2 := by
    obtain ⟨k, rfl⟩ := hodd
    simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
  have hn1 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
  have hmers : ¬ 3 ∣ 2 ^ n - 1 := by
    intro hd
    have h := Nat.mod_eq_zero_of_dvd hd
    omega
  have hnd : ¬ 3 ∣ n := by
    intro hd
    rcases (Nat.dvd_prime hn).mp hd with h | h <;> omega
  rw [c.card_group, hF, hΓ]
  intro hd
  rcases Nat.prime_three.dvd_mul.mp hd with h | h
  · rcases Nat.prime_three.dvd_mul.mp h with h | h
    · exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
    · exact hmers h
  · exact hnd h

/-- A faithful primitive action of even prime-power degree with trivial two-core
has no normal two-complement. -/
public theorem not_hasNormalTwoComplement {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
    [MulAction X F] [FaithfulSMul X F]
    (htwo : IsMultiplyPretransitive X F 2)
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (hcore : pCore 2 X = ⊥) : ¬ HasNormalPComplement 2 X := by
  intro h
  obtain ⟨N, hN, hcop, hquot⟩ := h
  let : N.Normal := hN
  let : IsPreprimitive X F := isPreprimitive_of_is_two_pretransitive htwo
  have hbot : N = ⊥ := by
    by_contra hne
    let : IsPretransitive N F := Atlas.GroupTheory.normal_pretransitive N hne
    have hd : Nat.card F ∣ Nat.card N := by
      rw [← index_stabilizer_of_transitive N (0 : F)]
      exact (stabilizer N (0 : F)).index_dvd_card
    have h2 : 2 ∣ Nat.card N := (dvd_pow_self 2 (by omega : n ≠ 0)).trans (hF ▸ hd)
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hcop) h2
  have hX : IsPGroup 2 X := by
    subst N
    exact hquot.of_equiv (QuotientGroup.quotientBot : X ⧸ (⊥ : Subgroup X) ≃* X)
  have htop : (⊤ : Subgroup X) ≤ pCore 2 X := le_sSup ⟨inferInstance, hX.to_subgroup ⊤⟩
  have hxb : (⊤ : Subgroup X) = ⊥ := le_bot_iff.mp (hcore ▸ htop)
  have hc : Nat.card X = 1 := by
    have hh := congrArg (fun H : Subgroup X => Nat.card H) hxb
    simpa using hh
  let : IsPretransitive X F := inferInstance
  have hdeg : Nat.card F ∣ Nat.card X := by
    rw [← index_stabilizer_of_transitive X (0 : F)]
    exact (stabilizer X (0 : F)).index_dvd_card
  rw [hc, Nat.dvd_one, hF] at hdeg
  exact (Nat.ne_of_gt (Nat.one_lt_pow (by omega) (by decide : 1 < 2))) hdeg



/-- Burnside transfer handles cyclic Sylow groups separately from the normal-four analysis. -/
public theorem sylow_not_isCyclic
    {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
    [MulAction X F] [FaithfulSMul X F]
    (htwo : IsMultiplyPretransitive X F 2)
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (hcore : pCore 2 X = ⊥) (S : Sylow 2 X) : ¬ IsCyclic S := by
  intro hcyc
  have heven : 2 ∣ Nat.card X := by
    let : IsPreprimitive X F := isPreprimitive_of_is_two_pretransitive htwo
    have hd : Nat.card F ∣ Nat.card X := by
      rw [← index_stabilizer_of_transitive X (0 : F)]
      exact (stabilizer X (0 : F)).index_dvd_card
    exact (dvd_pow_self 2 (by omega : n ≠ 0)).trans (hF ▸ hd)
  apply not_hasNormalTwoComplement htwo hn hF hcore
  exact BenderSuzuki.External.Suzuki.V.suzuki_ch5_theorem_2_10_corollary_1
    S ((Nat.minFac_eq_two_iff _).mpr heven) hcyc

/-- The source divisor (3G), conditional only on the remaining noncyclic-center assertion. -/
public theorem center_divisor_of_not_isCyclic
    {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
    [MulAction X F] [FaithfulSMul X F]
    (c : Coordinates X F) [IsPretransitive X F]
    {n : ℕ} (hodd : Odd n) (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n)
    (hfusion : ∀ z w : X, orderOf z = 2 → orderOf w = 2 → IsConj z w)
    (S : Sylow 2 X) (hcenter : ¬ IsCyclic (center S)) :
    ∃ r : ℕ, 1 < r ∧ r ≤ n ∧ 2 ^ r - 1 ∣ Nat.card (normalizer (S : Set X)) := by
  obtain ⟨r, hr, _, hbound, hd⟩ :=
    S.exists_omega_center_card_and_normalizer_divisor hcenter hfusion
  rw [sylow_card c hodd hn hF hΓ S] at hbound
  exact ⟨r, hr, (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hbound, hd⟩

/-- Assembly of the noncyclic-center assertion and (3G) from the two independent
local group-theoretic inputs. The normal four is intrinsic to S, and its
normalizer is taken after mapping it into the ambient group. -/
public theorem noncyclic_center_and_divisor_of_local_analysis
    {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
    [MulAction X F] [FaithfulSMul X F]
    (c : Coordinates X F) (htwo : IsMultiplyPretransitive X F 2)
    {n : ℕ} (hn : n.Prime) (hodd : Odd n) (hn3 : 3 < n)
    (hF : Nat.card F = 2 ^ n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n)
    (hcore : pCore 2 X = ⊥)
    (hfusion : ∀ z w : X, orderOf z = 2 → orderOf w = 2 → IsConj z w)
    (S : Sylow 2 X)
    (hnoFour : ¬ IsCyclic S →
      (¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4) →
      HasNormalPComplement 2 X)
    (hfour : IsCyclic (center S) →
      ∀ U : Subgroup S, U.Normal → IsElementaryAbelian 2 U → Nat.card U = 4 →
        3 ∣ Nat.card (normalizer (U.map (S : Subgroup X).subtype : Set X))) :
    ¬ IsCyclic (center S) ∧
      ∃ r : ℕ, 1 < r ∧ r ≤ n ∧ 2 ^ r - 1 ∣ Nat.card (normalizer (S : Set X)) := by
  let : IsPreprimitive X F := isPreprimitive_of_is_two_pretransitive htwo
  have hcenter : ¬ IsCyclic (center S) := by
    intro hcyc
    by_cases hU : ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4
    · obtain ⟨U, hUn, hUe, hUc⟩ := hU
      exact three_not_dvd_card c hn hodd hn3 hF hΓ
        ((hfour hcyc U hUn hUe hUc).trans
          (normalizer (U.map (S : Subgroup X).subtype : Set X)).card_subgroup_dvd_card)
    · exact not_hasNormalTwoComplement htwo hn.pos hF hcore
        (hnoFour (sylow_not_isCyclic htwo hn.pos hF hcore S) hU)
  exact ⟨hcenter, center_divisor_of_not_isCyclic c hodd hn.pos hF hΓ hfusion S hcenter⟩

/-- The noncyclic-center assertion of Lemma 3.10 and the divisor (3G), given
the lemma's independent involution-fusion assertion. The normal-complement
and Thompson normal-four premises are fully discharged. -/
public theorem noncyclic_center_and_divisor
    {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
    [MulAction X F] [FaithfulSMul X F]
    (c : Coordinates X F) (htwo : IsMultiplyPretransitive X F 2)
    {n : ℕ} (hn : n.Prime) (hodd : Odd n) (hn3 : 3 < n)
    (hF : Nat.card F = 2 ^ n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n)
    (hcore : pCore 2 X = ⊥)
    (hfusion : ∀ z w : X, orderOf z = 2 → orderOf w = 2 → IsConj z w)
    (S : Sylow 2 X) :
    ¬ IsCyclic (center S) ∧
      ∃ r : ℕ, 1 < r ∧ r ≤ n ∧ 2 ^ r - 1 ∣ Nat.card (normalizer (S : Set X)) := by
  let : IsPreprimitive X F := isPreprimitive_of_is_two_pretransitive htwo
  apply noncyclic_center_and_divisor_of_local_analysis c htwo hn hodd hn3 hF hΓ
    hcore hfusion S
  · intro hnoncyclic hno
    exact S.hasNormalTwoComplement_of_no_normal_four hnoncyclic
      (three_not_dvd_card c hn hodd hn3 hF hΓ) hno
  · intro hcenter U hUn hUe hUc
    let : U.Normal := hUn
    let : IsElementaryAbelian 2 U := hUe
    exact S.three_dvd_normalizer_card_of_normal_four hcenter hfusion U hUc

end MulAction.SemilinearPointStabilizer.PrimeExclusion
