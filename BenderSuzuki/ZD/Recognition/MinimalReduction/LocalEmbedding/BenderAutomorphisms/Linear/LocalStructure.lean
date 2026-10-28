module

public import BenderSuzuki.SE.Models
public import Theory.GroupAction.AutomorphismFixedTransport
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.FieldAction
public import Theory.SpecificGroups.SL2.SylowConsequences

/-!
# The inner-automorphism branch for binary PSL₂

The characteristic-two quotient equivalence transports the elementary abelian
Sylow groups of SL₂ and their nonnormality to PSL₂. If an inner automorphism
squares to one, the square of its conjugating element is central, hence trivial.
An elementary abelian Sylow subgroup containing that element lies in its
centralizer. For field degree at least two it contains a four-group. Thus a
fixed subgroup with no four-group forces the automorphism to be outer.

This proves the inner branch of the rank obstruction used in GLS, Volume 4,
Chapter 2, Proposition 4.4, from the structure in Chapter 4, Lemma 3.4(b).
No assertion about arbitrary outer automorphisms is used here.
-/

namespace BenderSuzuki.ZD.Linear
open _root_.BenderSuzuki.MatrixGroups PFAppendixIII PFchapter1section1

@[expose] public noncomputable def psl2SylowEquivAdditive {K : Type*} [Field K] [Finite K] [CharP K 2]
    (P : Sylow 2 (PSL2MatrixGroup K)) : Multiplicative K ≃* P := by
  let U := Matrix.SpecialLinearGroup.upperUnipotentSylow K 2
  let e := sl2QuotientEquiv K
  let Q := U.mapSurjective e.surjective
  have eU : U ≃* Q := by
    rw [show (Q : Subgroup (PSL2MatrixGroup K)) =
      (U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)).map e.toMonoidHom from
      Sylow.coe_mapSurjective e.surjective U]
    exact (U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)).equivMapOfInjective
      e.toMonoidHom e.injective
  exact (Matrix.SpecialLinearGroup.sylowEquivAdditive K 2 U).trans
    (eU.trans (Q.equiv P))

public theorem psl2_no_normal_sylow {K : Type*} [Field K] [Finite K] [CharP K 2] :
    ¬ ∃ P : Sylow 2 (PSL2MatrixGroup K), (P : Subgroup (PSL2MatrixGroup K)).Normal := by
  intro h
  obtain ⟨P, hP⟩ := ((sl2QuotientEquiv K).exists_normal_sylow_iff 2).mpr h
  exact Matrix.SpecialLinearGroup.no_normal_sylow K 2 P hP

public theorem binary_twoRank {n : ℕ} (hn : 2 ≤ n) :
    TwoRankAtLeastTwo (PSL2BinaryMatrixGroup n) := by
  obtain ⟨y, hy, hy1⟩ := Converse.exists_ne_zero_ne_one n hn
  exact Converse.twoRank y hy hy1

public theorem psl2_center_eq_bot {K : Type*} [Field K] [CharP K 2] :
    Subgroup.center (PSL2MatrixGroup K) = ⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨b, rfl⟩ := Converse.pi_surjective z
  have hb : b ∈ Subgroup.center (Converse.SL2 K) := by
    rw [Subgroup.mem_center_iff]
    intro c
    apply Converse.pi_injective
    simpa only [map_mul] using (Subgroup.mem_center_iff.mp hz) (Converse.pi K c)
  rw [Converse.center_SL2_eq_bot, Subgroup.mem_bot] at hb
  simp [hb]

public theorem inner_twoRank {n : ℕ} (hn : 2 ≤ n) (b : PSL2BinaryMatrixGroup n)
    (ha : (MulAut.conj b) ^ 2 = 1) :
    TwoRankAtLeastTwo (MulAut.conj b).fixedSubgroup := by
  have hb2 : b ^ 2 = 1 := by
    have hc : b ^ 2 ∈ Subgroup.center (PSL2BinaryMatrixGroup n) := by
      rw [Subgroup.mem_center_iff]
      intro x
      rw [← map_pow] at ha
      have h := congrArg (fun a : MulAut (PSL2BinaryMatrixGroup n) => a x) ha
      change b ^ 2 * x * (b ^ 2)⁻¹ = x at h
      exact ((mul_inv_eq_iff_eq_mul).mp h).symm
    simpa only [psl2_center_eq_bot, Subgroup.mem_bot] using hc
  have hz : IsPGroup 2 (Subgroup.zpowers b) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      simpa only [Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one hb2)
  obtain ⟨P, hP⟩ := hz.exists_le_sylow
  have hbP : b ∈ P := hP (Subgroup.mem_zpowers b)
  let e := psl2SylowEquivAdditive P
  have hcomm (x y : P) : x * y = y * x := by
    apply e.symm.injective
    simp only [map_mul, mul_comm]
  have hsq (x : P) : x ^ 2 = 1 := by
    apply e.symm.injective
    rw [map_pow, map_one]
    change 2 • (e.symm x).toAdd = 0
    exact (two_nsmul _).trans (CharTwo.add_self_eq_zero _)
  have hcard : Nat.card P = 2 ^ n := by
    rw [← Nat.card_congr e.toEquiv]
    exact Converse.card_binaryGaloisField n (by omega)
  have hdiv : 2 ^ 2 ∣ Nat.card P := by
    rw [hcard]
    exact Nat.pow_dvd_pow 2 hn
  obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdiv
  have hrank : TwoRankAtLeastTwo P := by
    refine ⟨E, by simpa using hE, fun x => ?_⟩
    apply Subtype.ext
    exact hsq x
  let f : P →* (MulAut.conj b).fixedSubgroup :=
    (P : Subgroup (PSL2BinaryMatrixGroup n)).subtype.codRestrict _ fun x => by
      rw [MulAut.mem_fixedSubgroup]
      change b * (x : PSL2BinaryMatrixGroup n) * b⁻¹ = x
      have hc := congrArg Subtype.val (hcomm ⟨b, hbP⟩ x)
      change b * (x : PSL2BinaryMatrixGroup n) = (x : PSL2BinaryMatrixGroup n) * b at hc
      rw [hc, mul_inv_cancel_right]
  apply hrank.map_of_injective f
  intro x y h
  have hh : (x : PSL2BinaryMatrixGroup n) = (y : PSL2BinaryMatrixGroup n) :=
    congrArg (fun z : (MulAut.conj b).fixedSubgroup => z.val) h
  exact Subtype.ext hh

public theorem fixed_no_four_implies_outer {n : ℕ} (hn : 2 ≤ n)
    (a : MulAut (PSL2BinaryMatrixGroup n)) (ha : a ^ 2 = 1)
    (hrank : ¬ TwoRankAtLeastTwo a.fixedSubgroup) :
    ¬ ∃ b : PSL2BinaryMatrixGroup n, a = MulAut.conj b := by
  rintro ⟨b, rfl⟩
  exact hrank (inner_twoRank hn b ha)

end BenderSuzuki.ZD.Linear
