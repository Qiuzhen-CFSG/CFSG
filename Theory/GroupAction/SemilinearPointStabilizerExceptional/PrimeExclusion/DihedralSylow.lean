module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeExclusion.Preparation
public import Theory.GroupAction.SubgroupCentralizerCongruence
public import Theory.GroupTheory.SpecificGroups.OddDihedralCentralizer

/-!
# Prime exclusion from Sylow two-normalizer orders

Let Γ have odd prime order n and an actual dihedral normalizer of order 2n.
If n divides a Sylow two-normalizer order, while occurring only once in the
ambient order, its conjugation action on the Sylow two-subgroups has a fixed
point T. The centralizer congruence then gives |T| ≡ |C_T(Γ)| modulo n.

The literal intersection C_T(Γ) is trivial. We use the equivalent transposed
centralizer argument in the dihedral model: if its image A were a nontrivial
two-subgroup, the image of Γ would lie in C(A), which is a two-group by the
explicit reflection calculation in `OddDihedralCentralizer`. This contradicts
|Γ| = n. Thus |T| = 2ⁿ ≡ 1 modulo n, contrary to Fermat's 2ⁿ ≡ 2.

The final theorem applies this argument to the literal two-point stabilizer
of the semilinear action and supplies the normalizer-order exclusion consumed
by `PrimeExclusion.false_of_center_divisor`. Neither involution fusion nor a
center-divisor assumption is needed here.

Source: GLS, Volume 4, Chapter 1, final argument of Theorem 3.2,
`refs/KGroup/GLS4/Chapter1.tex`, lines 456–468.
-/

public section

open Subgroup

namespace MulAction.SemilinearPointStabilizer.PrimeExclusion

/-- An odd-order subgroup with an actual odd-dihedral normalizer has trivial
centralizer in every two-subgroup. The maps are the literal inclusions into
the normalizer followed by the supplied model isomorphism. -/
theorem centralizer_intersection_bot
    {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : Odd n) (hnone : 1 < n)
    (Γ H : Subgroup G) (hΓ : Nat.card Γ = n) (hH : IsPGroup 2 H)
    (e : normalizer (Γ : Set G) ≃* DihedralGroup n) :
    H ⊓ centralizer (Γ : Set G) = ⊥ := by
  let : NeZero n := ⟨hn.pos.ne'⟩
  let N := normalizer (Γ : Set G)
  let C := H ⊓ centralizer (Γ : Set G)
  have hCN : C ≤ N := inf_le_right.trans (centralizer_le_normalizer _)
  let A := (C.subgroupOf N).map e.toMonoidHom
  let P := (Γ.subgroupOf N).map e.toMonoidHom
  have hA : IsPGroup 2 A :=
    ((hH.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe hCN).symm).map _
  have hPcard : Nat.card P = n := by
    rw [card_map_of_injective e.injective,
      Nat.card_congr (subgroupOfEquivOfLe (le_normalizer (H := Γ))).toEquiv, hΓ]
  have hPA : P ≤ centralizer (A : Set (DihedralGroup n)) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (hy.2 x hx).symm
  by_contra hne
  have hAne : A ≠ ⊥ := by
    intro hbot
    apply hne
    apply card_eq_one.mp
    have hc : Nat.card A = Nat.card C := by
      rw [card_map_of_injective e.injective,
        Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv]
    rw [← hc, hbot, card_bot]
  have hPtwo :=
    (DihedralGroup.isPGroup_centralizer_of_nontrivial_two_subgroup hn A hA hAne).to_le hPA
  obtain ⟨k, hk⟩ := hPtwo.exists_card_eq
  rw [hPcard] at hk
  have hkzero : k = 0 := by
    by_contra hkzero
    have hd : 2 ∣ n := hk ▸ dvd_pow_self 2 hkzero
    exact hn.not_two_dvd_nat hd
  simp [hkzero] at hk
  omega

/-- A prime occurring only once in the ambient order and dividing a Sylow
two-normalizer order makes every subgroup of that prime order normalize some
Sylow two-subgroup. The action is ambient conjugation on Sylow subgroups. -/
theorem normalizing_sylow_of_dvd
    {G : Type*} [Group G] [Finite G] {n m : ℕ} (hn : n.Prime)
    (hG : Nat.card G = m * n) (hcop : Nat.Coprime n m)
    (Γ : Subgroup G) (hΓ : Nat.card Γ = n) (S : Sylow 2 G)
    (hd : n ∣ Nat.card (normalizer (S : Set G))) :
    ∃ T : Sylow 2 G, Γ ≤ normalizer (T : Set G) := by
  let : Fact n.Prime := ⟨hn⟩
  have hΓp : IsPGroup n Γ := IsPGroup.of_card (hΓ.trans (pow_one n).symm)
  have hcount : ¬ n ∣ Nat.card (Sylow 2 G) := by
    rw [S.card_eq_index_normalizer]
    obtain ⟨k, hk⟩ := hd
    have he := (normalizer (S : Set G)).index_mul_card
    rw [hk, hG] at he
    have he' : (normalizer (S : Set G)).index * k = m := by
      apply Nat.eq_of_mul_eq_mul_right hn.pos
      simpa only [mul_assoc, mul_comm n k] using he
    intro hdiv
    apply hn.coprime_iff_not_dvd.mp hcop
    rw [← he']
    exact dvd_mul_of_dvd_left hdiv k
  obtain ⟨T, hT⟩ := hΓp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 G) hcount
  exact ⟨T, Γ.sylow_mem_fixedPoints_iff.mp hT⟩

/-- The prime binary degree does not divide any Sylow two-normalizer order
when the literal two-point stabilizer has order n and its normalizer has an
actual dihedral model. This discharges the normalizer-order premise of the
final center-divisor contradiction. -/
theorem prime_not_dvd_sylow_normalizer
    {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
    [MulAction X F] [FaithfulSMul X F] [IsPretransitive X F]
    (c : Coordinates X F) {n : ℕ} (hn : n.Prime) (hodd : Odd n)
    (hF : Nat.card F = 2 ^ n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n)
    (hD : Nonempty ((normalizer (twoPoint (X := X) (F := F) : Set X)) ≃*
      DihedralGroup n)) (S : Sylow 2 X) :
    ¬ n ∣ Nat.card (normalizer (S : Set X)) := by
  let : Fact n.Prime := ⟨hn⟩
  intro hd
  have hX : Nat.card X = (2 ^ n * (2 ^ n - 1)) * n := by
    rw [c.card_group, hF, hΓ]
  have hcop : Nat.Coprime n (2 ^ n * (2 ^ n - 1)) :=
    (hodd.coprime_two_right.pow_right n).mul_right (prime_coprime_mersenne hn)
  obtain ⟨T, hT⟩ := normalizing_sylow_of_dvd hn hX hcop
    (twoPoint (X := X) (F := F)) hΓ S hd
  obtain ⟨e⟩ := hD
  have hC := centralizer_intersection_bot hodd hn.one_lt
    (twoPoint (X := X) (F := F)) (T : Subgroup X) hΓ T.isPGroup' e
  have hΓp : IsPGroup n (twoPoint (X := X) (F := F)) :=
    IsPGroup.of_card (hΓ.trans (pow_one n).symm)
  have hm := card_modEq_card_inf_centralizer _ (T : Subgroup X) hΓp hT
  rw [sylow_card c hodd hn.pos hF hΓ T, hC, card_bot] at hm
  have hz := (ZMod.natCast_eq_natCast_iff (2 ^ n) 1 n).mpr hm
  rw [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, ZMod.pow_card] at hz
  have hzero : (1 : ZMod n) = 0 := by linear_combination hz
  exact one_ne_zero hzero

end MulAction.SemilinearPointStabilizer.PrimeExclusion
