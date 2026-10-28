module
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupAction.AbelianCoprimeFixedGeneration
public import Theory.GroupAction.Lemmas

/-!
# Excluding elementary ternary rank four in binary dimension six

An elementary abelian group of order 81 cannot embed in the automorphism
group of an elementary abelian two-group of order at most 64.

Cyclic-quotient fixed-point generation supplies fixed factors for actor
subgroups K of index at most three, hence of order at least 27. If a fixed
factor had order at least four, coprime splitting would give a faithful
K-action on a complementary factor of order at most sixteen. But 27 does
not divide the order of its general linear group. Thus every generating
fixed factor has order at most two and is fixed by the whole actor. The
whole action is trivial, contradicting faithfulness.

The fixed-point generation input is Feit–Thompson background Proposition
(1.16)(b), formalized in `AbelianCoprimeFixedGeneration`. The remaining
steps are coprime splitting and the finite general-linear order formula.
-/

open Subgroup
open scoped IsMulCommutative

private instance elementary_subgroup
    {E : Type*} [Group E] [IsElementaryAbelian 2 E] (D : Subgroup E) :
    IsElementaryAbelian 2 D where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := (Monoid.exponent_dvd_of_monoidHom D.subtype D.subtype_injective).trans
    (IsElementaryAbelian.exponent_dvd_p 2 E)

private theorem not_twentyseven_dvd_small_binary_aut
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 16) : ¬ 27 ∣ Nat.card (MulAut E) := by
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hnle : n ≤ 4 := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    rw [← hn] at hp
    norm_num at hp
    omega
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E n hn]
  interval_cases n <;> decide

private theorem fixed_card_lt_four
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 64) (A : Subgroup (MulAut E))
    [IsElementaryAbelian 3 A] (hA : Nat.card A = 81)
    (K : Subgroup A) (hK : IsCyclic (A ⧸ K)) :
    Nat.card (FixedPoints.subgroup K E) < 4 := by
  have hquot : Nat.card (A ⧸ K) ≤ 3 := by
    apply Nat.le_of_dvd (by decide)
    rw [← hK.exponent_eq_card]
    exact (Group.exponent_quotient_dvd K).trans
      (IsElementaryAbelian.exponent_dvd_p 3 A)
  have hKbound : 27 ≤ Nat.card K := by
    have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    rw [hA] at hh
    nlinarith
  have hpK := (IsElementaryAbelian.isPGroup 3 A).to_subgroup K
  obtain ⟨k, hk⟩ := hpK.exists_card_eq
  have h27 : 27 ∣ Nat.card K := by
    have hkle : 3 ≤ k := by
      by_contra! hh
      have hp := Nat.pow_le_pow_right (by decide : 0 < 3) (show k ≤ 2 by omega)
      rw [← hk] at hp
      norm_num at hp
      omega
    rw [hk]
    exact pow_dvd_pow 3 hkle
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hcop : Nat.Coprime (Nat.card K) (Nat.card E) := by
    rw [hk, hn]
    exact ((by decide : Nat.Coprime 3 2).pow_left k).pow_right n
  let F := FixedPoints.subgroup K E
  let C := commutatorAction K E
  have hcompl : IsCompl F C :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm (fun a b : E => mul_comm a b)) hcop inferInstance
  have hprod : Nat.card F * Nat.card C = Nat.card E := by
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint F C
      (by rw [normalizer_eq_top]; exact le_top) hcompl.disjoint
    rw [hcompl.sup_eq_top, card_top] at hh
    exact hh.symm
  by_contra! hlarge
  have hC : Nat.card C ≤ 16 := by
    change 4 ≤ Nat.card F at hlarge
    nlinarith
  let : IsInvariant K E C := commutatorAction_isInvariant
  let f := MulDistribMulAction.toMulAut K C
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro a ha
    apply mem_bot.mpr
    apply Subtype.ext
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp
      (show x ∈ F ⊔ C by rw [hcompl.sup_eq_top]; trivial)
    have hfixy : (a.val.val : MulAut E) y = y := hy a
    have hfixz : (a.val.val : MulAut E) z = z :=
      congrArg Subtype.val (MulEquiv.congr_fun (MonoidHom.mem_ker.mp ha) ⟨z, hz⟩)
    change (a.val.val : MulAut E) (y * z) = y * z
    rw [map_mul, hfixy, hfixz]
  exact not_twentyseven_dvd_small_binary_aut hC
    (h27.trans (Subgroup.card_dvd_of_injective f hf))

/-- Binary dimension at most six excludes a faithful elementary ternary actor of order 81. -/
public theorem not_card_eightyone_elementary_three_subgroup_binary_le_sixtyfour
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 64) (A : Subgroup (MulAut E))
    [IsElementaryAbelian 3 A] : Nat.card A ≠ 81 := by
  intro hA
  let : CommGroup A := IsMulCommutative.instCommGroup
  let : Fact (IsPGroup 2 E) := ⟨IsElementaryAbelian.isPGroup 2 E⟩
  have hgen := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup
    (G := E) (A := A) (q := 2)
    (show Nat.Coprime (Nat.card A) 2 by rw [hA]; decide)
  have hfixed (K : Subgroup A) (hK : IsCyclic (A ⧸ K)) :
      FixedPoints.subgroup K E ≤ FixedPoints.subgroup A E := by
    let C := FixedPoints.subgroup K E
    have hsmall := fixed_card_lt_four hE A hA K hK
    change Nat.card C < 4 at hsmall
    have hstable (a : A) (x : E) (hx : x ∈ C) : a • x ∈ C := by
      intro k
      change (k : A) • (a • x) = a • x
      rw [← mul_smul, mul_comm (k : A), mul_smul]
      exact congrArg (fun y : E => a • y) (hx k)
    let : IsInvariant A E C := ⟨fun a x => ⟨hstable a x, fun h => by
      have hh := hstable a⁻¹ (a • x) h
      simpa only [inv_smul_smul] using hh⟩⟩
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 C).exists_card_eq
    have hnle : n ≤ 1 := by
      by_contra! hh
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
      rw [← hn] at hp
      norm_num at hp
      omega
    have hAut : Nat.card (MulAut C) = 1 := by
      rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow C n hn]
      interval_cases n <;> decide
    let : Subsingleton (MulAut C) := (Nat.card_eq_one_iff_unique.mp hAut).1
    intro x hx a
    have hh : MulDistribMulAction.toMulAut A C a = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val (MulEquiv.congr_fun hh ⟨x, hx⟩)
  have htop : FixedPoints.subgroup A E = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact iSup₂_le hfixed
  have hbot : A = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    apply mem_bot.mpr
    apply MulEquiv.ext
    intro x
    exact (show x ∈ FixedPoints.subgroup A E from htop ▸ mem_top x) ⟨a, ha⟩
  rw [hbot, card_bot] at hA
  norm_num at hA
