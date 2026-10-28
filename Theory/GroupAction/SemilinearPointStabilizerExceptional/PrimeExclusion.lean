module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeExclusion.Preparation
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeExclusion.InvolutionFusion
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeExclusion.CenterDivisor
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeExclusion.DihedralSylow

/-!
# The final Sylow-normalizer contradiction in prime degree

Assume the scalars normally generate the permutation group and the degree is
2ⁿ for an odd prime n. Given a Sylow two-subgroup S, a divisor 2ʳ−1 of |N(S)|
with 1 < r ≤ n, and n ∤ |N(S)|, the action is impossible. A smaller exponent
would give 2ʳ−1 = n. At r = n the normalizer has order 2ⁿ(2ⁿ−1), and its zero
stabilizer is the normal Hall subgroup K of the semilinear stabilizer.
Transitivity then puts every conjugate of K in N(S), forcing N(S) = X.

The final theorem supplies both inputs: involution fusion and the noncyclic
Sylow-center argument give the center divisor, while the fixed-point congruence
in the actual dihedral normalizer of the two-point stabilizer gives n ∤ |N(S)|.
Thus no such action exists at odd prime degree exponent n > 3 with trivial
two-core, scalar normal generation, |Γ| = n and N(Γ) ≃ D₂ₙ. The numerical and
dihedral hypotheses remain explicit outputs of the earlier prime reduction.

Source: GLS, Volume 4, Chapter 1, Lemma 3.10 and the final argument of
Theorem 3.2 (`refs/KGroup/GLS4/Chapter1.tex`, lines 450–468).
-/

public section

namespace MulAction.SemilinearPointStabilizer.PrimeExclusion

variable {X F : Type*} [Group X] [Field F] [MulAction X F] [FaithfulSMul X F]

/-- A transitive subgroup containing K contains its ambient normal closure. -/
lemma scalarClosure_le_of_transitive (c : Coordinates X F) (N : Subgroup X)
    [IsPretransitive N F] (hK : c.scalarSubgroup ≤ N) : c.scalarClosure ≤ N := by
  change Subgroup.closure (Group.conjugatesOfSet (c.scalarSubgroup : Set X)) ≤ N
  rw [Subgroup.closure_le]
  intro x hx
  obtain ⟨k, hk, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
  obtain ⟨u, hu⟩ := exists_smul_eq N (0 : F) (g • (0 : F))
  have hb : (u : X)⁻¹ * g ∈ stabilizer X (0 : F) := by
    change ((u : X)⁻¹ * g) • (0 : F) = 0
    rw [mul_smul, ← hu]
    exact inv_smul_smul (u : X) (0 : F)
  have hconj := (Subgroup.mem_normalizer_iff.mp
    (c.stabilizer_le_scalar_normalizer hb) k).mp hk
  have he : g * k * g⁻¹ = (u : X) * (((u : X)⁻¹ * g) * k *
      ((u : X)⁻¹ * g)⁻¹) * (u : X)⁻¹ := by group
  rw [he]
  exact N.mul_mem (N.mul_mem u.property (hK hconj)) (N.inv_mem u.property)

variable [Finite X] [Finite F]

/-- Inside the zero stabilizer, a subgroup of scalar order is exactly K. -/
lemma scalar_eq_of_order (c : Coordinates X F) {n : ℕ}
    (hn : n.Prime) (hF : Nat.card F = 2 ^ n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n)
    (H : Subgroup X) (hH : H ≤ stabilizer X (0 : F))
    (hcard : Nat.card H = 2 ^ n - 1) : H = c.scalarSubgroup := by
  let B := stabilizer X (0 : F)
  let K := c.scalarSubgroup.subgroupOf B
  let J := H.subgroupOf B
  have hK : Nat.card K = 2 ^ n - 1 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.scalarSubgroup_le_stabilizer).toEquiv,
      scalar_card c, hF]
  have hJ : Nat.card J = 2 ^ n - 1 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv, hcard]
  have hB : Nat.card B = (2 ^ n - 1) * n := by rw [c.card_stabilizer, hF, hΓ]
  have hmpos : 0 < 2 ^ n - 1 := by
    have := Nat.one_lt_pow hn.ne_zero (by decide : 1 < 2)
    omega
  have hindex : K.index = n := by
    have he := K.card_mul_index
    rw [hK, hB] at he
    exact Nat.eq_of_mul_eq_mul_left hmpos he
  let : K.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer
    c.scalarSubgroup_le_stabilizer).mpr c.stabilizer_le_scalar_normalizer
  have hle : J ≤ K := by
    apply Subgroup.relIndex_eq_one.mp
    apply Nat.eq_one_of_dvd_coprimes (prime_coprime_mersenne hn)
    · simpa only [hindex] using K.relIndex_dvd_index_of_normal J
    · simpa only [hJ] using K.relIndex_dvd_card J
  have hHK : H ≤ c.scalarSubgroup := fun x hx => hle (show (⟨x, hH hx⟩ : B) ∈ J from hx)
  exact Subgroup.eq_of_le_of_card_ge hHK (by rw [scalar_card c, hF, hcard])

/-- At the full center exponent, scalar normal generation forces N(S) = X. -/
lemma normalizer_eq_top_of_mersenne_dvd (c : Coordinates X F) [IsPretransitive X F]
    {n : ℕ} (hn : n.Prime) (hodd : Odd n) (hF : Nat.card F = 2 ^ n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n)
    (hgen : c.scalarClosure = ⊤) (S : Sylow 2 X)
    (hnd : ¬ n ∣ Nat.card (Subgroup.normalizer (S : Set X)))
    (hd : 2 ^ n - 1 ∣ Nat.card (Subgroup.normalizer (S : Set X))) :
    Subgroup.normalizer (S : Set X) = ⊤ := by
  let N := Subgroup.normalizer (S : Set X)
  have hS := sylow_card c hodd hn.pos hF hΓ S
  have hlow : 2 ^ n * (2 ^ n - 1) ∣ Nat.card N := by
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      ((mersenne_coprime_two hn.pos).symm.pow_left n)
    · rw [← hS]
      exact Subgroup.card_dvd_of_le Subgroup.le_normalizer
    · exact hd
  have hupp : Nat.card N ∣ 2 ^ n * (2 ^ n - 1) := by
    apply (hn.coprime_iff_not_dvd.mpr hnd).symm.dvd_of_dvd_mul_right
    have h := N.card_subgroup_dvd_card
    rwa [c.card_group, hF, hΓ] at h
  have hN : Nat.card N = 2 ^ n * (2 ^ n - 1) := Nat.dvd_antisymm hupp hlow
  let : IsPretransitive S F := sylow_transitive c hodd hn.pos hF hΓ S
  let : IsPretransitive N F := ⟨fun x y => by
    obtain ⟨s, hs⟩ := exists_smul_eq S x y
    exact ⟨⟨s, Subgroup.le_normalizer s.property⟩, hs⟩⟩
  let H := N ⊓ stabilizer X (0 : F)
  have hHcard : Nat.card H = 2 ^ n - 1 := by
    let e : stabilizer N (0 : F) ≃ H :=
      { toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
        invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have he := (stabilizer N (0 : F)).index_mul_card
    rw [index_stabilizer_of_transitive, hF, hN, Nat.card_congr e] at he
    exact Nat.eq_of_mul_eq_mul_left (by positivity) he
  have hK : c.scalarSubgroup ≤ N := by
    rw [← scalar_eq_of_order c hn hF hΓ H inf_le_right hHcard]
    exact inf_le_left
  have hc := scalarClosure_le_of_transitive c N hK
  rw [hgen] at hc
  exact top_unique hc

/-- Final contradiction from the center divisor and the dihedral-normalizer
prime exclusion. The final theorem below supplies both displayed inputs. -/
lemma false_of_center_divisor (c : Coordinates X F) [IsPretransitive X F]
    {n : ℕ} (hn : n.Prime) (hodd : Odd n) (hF : Nat.card F = 2 ^ n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n)
    (hgen : c.scalarClosure = ⊤) (S : Sylow 2 X)
    (hnd : ¬ n ∣ Nat.card (Subgroup.normalizer (S : Set X)))
    {r : ℕ} (hr : 1 < r) (hrn : r ≤ n)
    (hd : 2 ^ r - 1 ∣ Nat.card (Subgroup.normalizer (S : Set X))) : False := by
  have heq : r = n := by
    by_contra hne
    have hdX := hd.trans (Subgroup.normalizer (S : Set X)).card_subgroup_dvd_card
    rw [c.card_group, hF, hΓ] at hdX
    have he := small_mersenne_eq_prime hn hr (lt_of_le_of_ne hrn hne) hdX
    exact hnd (he ▸ hd)
  subst r
  have hN := normalizer_eq_top_of_mersenne_dvd c hn hodd hF hΓ hgen S hnd hd
  apply hnd
  rw [hN, Subgroup.card_top, c.card_group, hF, hΓ]
  exact dvd_mul_left _ _

/-- The prime-reduced semilinear action cannot have binary degree exponent
greater than three. All fusion, Sylow-center and normalizer-order premises
of the final contradiction are discharged; the explicit numerical and actual
dihedral-model hypotheses are the preceding Lemma 3.9 inputs. -/
theorem false_of_prime_degree_gt_three (c : Coordinates X F)
    (htwo : IsMultiplyPretransitive X F 2)
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hcore : pCore 2 X = ⊥)
    (hgen : c.scalarClosure = ⊤) (hn : n.Prime) (hodd : Odd n) (hn3 : 3 < n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n)
    (hdihedral : Nonempty ((Subgroup.normalizer (twoPoint (X := X) (F := F) : Set X)) ≃*
      DihedralGroup n)) : False := by
  let _ : IsMultiplyPretransitive X F 2 := htwo
  let _ : IsPretransitive X F := isPretransitive_of_is_two_pretransitive
  let S : Sylow 2 X := Classical.choice inferInstance
  have hfusion := involutions_isConj c htwo hF hcore hgen hn hodd hn3 hΓ hdihedral
  obtain ⟨_, r, hr, hrn, hd⟩ :=
    noncyclic_center_and_divisor c htwo hn hodd hn3 hF hΓ hcore hfusion S
  have hnd := prime_not_dvd_sylow_normalizer c hn hodd hF hΓ hdihedral S
  exact false_of_center_divisor c hn hodd hF hΓ hgen S hnd hr hrn hd

end MulAction.SemilinearPointStabilizer.PrimeExclusion
