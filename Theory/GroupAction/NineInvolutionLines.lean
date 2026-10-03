module

public import Theory.GroupAction.CoprimeHall
public import Theory.GroupTheory.Commutator.ActionTriviality
public import Theory.ElementaryAbelian.Basic

/-!
# The two lines of a non-scalar involution on an elementary group of order nine

An involution acting neither trivially nor by inversion on an elementary
abelian group of order nine has fixed and commutator subgroups of order
three. It acts by inversion on the latter. The statement uses the given
action restricted to the exact cyclic actor subgroup, with no alternate
action instance.

The proof checks inversion on action-commutator generators and extends it
through their closure. Coprime action splits the module into fixed and
commutator parts. Nontrivial action excludes a trivial commutator part;
non-inversion excludes a trivial fixed part. Their cardinal product nine
forces both parts to have order three.

This supplies the two complementary lines used to identify the exceptional
group in Stellmacher (1.6), journal p.18.
Source: `refs/latex/stellmacher-n-group.tex`.
-/

open scoped IsMulCommutative Pointwise

public theorem involution_fixed_commutator_card_three
    {A W : Type*} [Group A] [Group W] [Finite A] [Finite W]
    [IsElementaryAbelian 3 W] [MulDistribMulAction A W]
    (a : A) (ha2 : a ^ 2 = 1) (hW : Nat.card W = 9)
    (hne : ¬ ∀ w : W, a • w = w)
    (hninv : ¬ ∀ w : W, a • w = w⁻¹) :
    Nat.card (FixedPoints.subgroup (Subgroup.zpowers a) W) = 3 ∧
      Nat.card (commutatorAction (Subgroup.zpowers a) W) = 3 ∧
      ∀ w ∈ commutatorAction (Subgroup.zpowers a) W, a • w = w⁻¹ := by
  let P := Subgroup.zpowers a
  let C := FixedPoints.subgroup P W
  let D := commutatorAction P W
  have ha1 : a ≠ 1 := by intro heq; apply hne; simp [heq]
  have hPcard : Nat.card P = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha2 ha1]
  have haa (w : W) : a • (a • w) = w := by
    rw [smul_smul, ← pow_two, ha2, one_smul]
  have hPmem (p : P) : (p : A) = 1 ∨ (p : A) = a := by
    have hp := Subgroup.mem_zpowers_iff.mp p.property
    obtain ⟨n, hn⟩ := hp
    have hcases := Int.emod_two_eq_zero_or_one n
    have hred : a ^ n = a ^ (n % 2) := by
      simpa only [orderOf_eq_prime ha2 ha1, Nat.cast_ofNat] using (zpow_mod_orderOf a n).symm
    rcases hcases with h | h
    · left; rw [← hn, hred, h]; simp
    · right; rw [← hn, hred, h]; simp
  have hinv : ∀ w ∈ D, a • w = w⁻¹ := by
    intro w hw
    change w ∈ commutatorAction P W at hw
    rw [commutatorAction_eq_closure] at hw
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
        obtain ⟨p, x, rfl⟩ := hw
        rcases hPmem p with hp | hp
        · change a • (x⁻¹ * ((p : A) • x)) = (x⁻¹ * ((p : A) • x))⁻¹
          simp [hp]
        · change a • (x⁻¹ * ((p : A) • x)) = (x⁻¹ * ((p : A) • x))⁻¹
          rw [hp, smul_mul', smul_inv', haa, mul_inv_rev, inv_inv]
    | one => simp
    | mul x y _ _ hx hy => simp only [smul_mul', hx, hy, mul_inv_rev]; exact mul_comm _ _
    | inv x _ hx => simp only [smul_inv', hx]
  have hcop : Nat.Coprime (Nat.card P) (Nat.card W) := by rw [hPcard, hW]; decide
  have hcomp : IsCompl C D :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := W) (A := P)
      (Group.isSolvable_of_comm fun x y => IsMulCommutative.is_comm.comm x y) hcop inferInstance
  have hDne : D ≠ ⊥ := by
    intro hd
    have htriv := actsTrivially_of_commutatorAction_eq_bot hd
    exact hne (fun w => htriv ⟨a, Subgroup.mem_zpowers a⟩ w)
  have hCne : C ≠ ⊥ := by
    intro hc
    have hd : D = ⊤ := by simpa only [hc, bot_sup_eq] using hcomp.sup_eq_top
    exact hninv (fun w => hinv w (hd ▸ Subgroup.mem_top w))
  have hDpos : 1 < Nat.card D := by
    exact Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot D).mpr hDne)
  have hmul : Nat.card C * Nat.card D = 9 := by
    let _ : C.Normal := Subgroup.normal_of_isMulCommutative C
    have hc : C.IsComplement' D := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
      hcomp.disjoint (by rw [← Subgroup.normal_mul, hcomp.sup_eq_top]; rfl)
    exact hc.card_mul_card.trans hW
  have hCdvd : Nat.card C ∣ 9 := ⟨Nat.card D, hmul.symm⟩
  have hc3 : Nat.card C = 3 := by
    have h := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp (show Nat.card C ∣ 3^2 by exact hCdvd)
    obtain ⟨k, hk, heq⟩ := h
    interval_cases k
    · norm_num at heq
      exact (hCne heq).elim
    · norm_num at heq
      exact heq
    · norm_num at heq
      rw [heq] at hmul
      omega
  have hd3 : Nat.card D = 3 := by rw [hc3] at hmul; omega
  exact ⟨hc3, hd3, hinv⟩

