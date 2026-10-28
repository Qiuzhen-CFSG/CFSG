module
public import CFSG.Quasithin.ChapterF.Section01.RankOneSmallTwoPart
public import BenderSuzuki.SE.ModelSylowInvolutions
public import GorensteinWalter.PSL2DihedralSylow
public import GorensteinWalter.LinearRingEquiv
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# The odd-prime overlap of the source rank-one models

A nonsolvable simple model in F.1.1 is a simple Bender model. The special
unitary alternative is first projected through its actual central kernel;
simplicity and nonsolvability make that kernel trivial. The degenerate
linear, Suzuki and unitary parameters are excluded by their proved solvability.

In a simple Bender model, two involutions in a two-subgroup commute.
A dihedral Sylow can therefore have order at most four. For an odd-prime
PSL₂ model this forces the binary rank-one alternative PSL₂(4), and its
order forces the odd prime to be five.

The consumer is the complete odd quadratic-field containing-component
exclusion in the smaller changed-Sylow branch of original 5.2.2.
Source: Aschbacher–Smith F.1.1, A.3.12(8) and 5.2.2,
printed pp.259,47–48,648–649 (`refs/quasithin.pdf`); the commuting-involution
fact is Peterfalvi I.1.1(c), I.2.1(c), through the three concrete converses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source
variable {X : Type*} [Group X] [Finite X]

private theorem unitary_bender {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSU X 3 (2 ^ n)) (hns : ¬ Group.IsSolvable X) :
    BenderSuzuki.IsSimpleBenderGroup X := by
  obtain ⟨F,_,_,J,hF,hj,⟨e⟩⟩ := hm
  have hn1 : n ≠ 1 := by
    intro he
    subst n
    let := HermitianForm.FixedFieldTwo.projective_isSolvable J
      (by simpa using hF) (by simpa using hj)
    exact hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hF hj
  obtain ⟨a⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2 ^ n) hF hfixed
  exact .isPSU3 ⟨n,by omega,F,inferInstance,inferInstance,
    HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J,
    rfl,hF,hfixed,⟨e.trans a⟩⟩

/-- A nonsolvable simple source rank-one model is one of the simple Bender carriers. -/
theorem IsRankOneModel.simple_bender [IsSimpleGroup X]
    (hm : IsRankOneModel X) (hns : ¬ Group.IsSolvable X) :
    BenderSuzuki.IsSimpleBenderGroup X := by
  cases hm with
  | linear n hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have hn1 : n ≠ 1 := by
      intro he
      subst n
      obtain ⟨a⟩ := BenderSuzuki.External.huppert_II_6_14_a_psl2_card_two
        (show Nat.card F = 2 by simpa using hF)
      let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
        apply isSolvable_of_prime_dvd_card_eq_two_or_three
        intro p hp hd
        have hh : p ∣ 2 * 3 := by
          simpa only [Nat.card_perm,Nat.card_fin,Nat.factorial] using hd
        exact (hp.dvd_mul.mp hh).imp
          ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp)
          ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp)
      exact hns (Group.isSolvable_of_isSolvable_injective
        (f := (e.trans a).toMonoidHom) (e.trans a).injective)
    let : Fintype F := Fintype.ofFinite F
    let : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    let a : F ≃+* GaloisField 2 n := FiniteField.ringEquivOfCardEq (by
      rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hF,
        GaloisField.card 2 n (by omega)])
    exact .isPSL2 ⟨n,by omega,⟨e.trans (GorensteinWalter.psl2RingEquiv a)⟩⟩
  | suzuki m hm =>
    by_cases hm0 : m = 0
    · subst m
      let := suzukiZero_isSolvable
      exact (hns (Group.isSolvable_of_isSolvable_injective
        (f := hm.some.toMonoidHom) hm.some.injective)).elim
    · exact .isSuzuki ⟨m,by omega,hm⟩
  | projective_unitary n hn hm => exact unitary_bender hn hm hns
  | special_unitary n hn hm =>
    obtain ⟨F,_,_,J,hF,hj,⟨e⟩⟩ := hm
    let : IsSimpleGroup J.specialSubgroup := e.symm.isSimpleGroup
    have hk : J.specialToProjective.ker = ⊥ := by
      apply (inferInstance : J.specialToProjective.ker.Normal).eq_bot_or_eq_top.resolve_right
      intro ht
      have hc : (⊤ : Subgroup J.specialSubgroup) ≤ center J.specialSubgroup :=
        ht ▸ J.specialToProjective_ker_le_center
      let : IsMulCommutative J.specialSubgroup := center_eq_top_iff.mp (top_unique hc)
      let : Group.IsSolvable J.specialSubgroup := Group.isSolvable_of_comm
        fun a b => IsMulCommutative.is_comm.comm a b
      exact hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
    let a := MulEquiv.ofBijective J.specialToProjective
      ⟨(MonoidHom.ker_eq_bot_iff _).mp hk,J.specialToProjective_surjective⟩
    exact unitary_bender hn ⟨F,inferInstance,inferInstance,J,hF,hj,⟨e.trans a⟩⟩ hns
  | dihedral hm =>
    let := GLS3.Chapter5.dihedralGroup_isSolvable 5
    exact (hns (Group.isSolvable_of_isSolvable_injective
      (f := hm.some.toMonoidHom) hm.some.injective)).elim

private theorem sylow_card_le_four_of_dihedral
    (hm : BenderSuzuki.IsSimpleBenderGroup X) (S : Sylow 2 X)
    {m : ℕ} (e : S ≃* DihedralGroup (2 ^ m)) : Nat.card S ≤ 4 := by
  let a := e.symm (DihedralGroup.sr 0)
  let b := e.symm (DihedralGroup.sr 1)
  have ha : a ^ 2 = 1 := e.injective (by simp [a,pow_two])
  have hb : b ^ 2 = 1 := e.injective (by simp [b,pow_two])
  have hc := hm.squares_commute_in_twoSubgroup (S : Subgroup X) S.isPGroup'
    a b a.property b.property (congrArg Subtype.val ha) (congrArg Subtype.val hb)
  have hc' : a*b=b*a := Subtype.ext hc.eq
  have he : (1 : ZMod (2 ^ m)) = -1 := by
    have hh := congrArg e hc'
    simpa [a,b,DihedralGroup.sr_mul_sr] using hh
  have hd : 2 ^ m ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (2 ^ m)).mp (by
    change (2 : ZMod (2 ^ m)) = 0
    calc
      2 = (1 : ZMod (2 ^ m)) + 1 := by ring
      _ = 0 := add_eq_zero_iff_eq_neg.mpr he)
  rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

/-- The odd-prime PSL₂ overlap of the nonsolvable source rank-one models is PSL₂(5). -/
theorem IsRankOneModel.odd_prime_parameter
    (hr : IsRankOneModel X) (hns : ¬ Group.IsSolvable X)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hgt : 3 < p)
    (hm : ClassicalGroup.IsPSL X 2 p) : p = 5 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : IsSimpleGroup X := e.isSimpleGroup_congr.mpr
    (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega))
  have hb := hr.simple_bender hns
  let S : Sylow 2 X := Sylow.nonempty.some
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨m,_,⟨a⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F
    ⟨p,1,hp,ho,by decide,by simpa using hF⟩ P
  let b : S ≃* P := (S : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective
  have hS := sylow_card_le_four_of_dihedral hb S (b.trans a)
  have hsmall : ¬16 ∣ Nat.card X := by
    intro hd
    have hh := S.pow_dvd_card_of_pow_dvd_card (n := 4) hd
    have := Nat.le_of_dvd (Nat.card_pos (α := S)) hh
    norm_num at this
    omega
  obtain ⟨f,hf,hf3,F₂,_,_,hF₂,⟨e₂⟩⟩ := hr.binary_of_small_twoPart hns hsmall
  let : Fintype F₂ := Fintype.ofFinite F₂
  let : CharP F₂ 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF₂)
  have horder := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F₂)
  rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (CharTwo.neg_eq 1),mul_one,hF₂,←Nat.card_congr e₂.toEquiv] at horder
  have hd : 2 ^ f ∣ Nat.card X := by rw [horder]; exact dvd_mul_right _ _
  have hpow := Nat.le_of_dvd (Nat.card_pos (α := S))
    (S.pow_dvd_card_of_pow_dvd_card hd)
  have hf2 : f = 2 := by
    have hcases : f = 2 ∨ f = 3 := by omega
    rcases hcases with he | he
    · exact he
    · norm_num [he] at hpow
      omega
  have hc : Nat.card X = 60 := by norm_num [hf2] at horder; exact horder
  have hodd := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (hF.symm ▸ ho)
  rw [hF,←Nat.card_congr e.toEquiv,hc] at hodd
  have hp5 : p ≤ 5 := by
    by_contra hh
    have hs : 35 ≤ p ^ 2 - 1 := by
      have : 36 ≤ p ^ 2 := by nlinarith
      omega
    nlinarith
  have hpne4 : p ≠ 4 := by intro he; norm_num [he] at hp
  omega
end CFSG.Quasithin.ChapterF.Source
