module

public import Theory.Comparator.Defs
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Solvable
import BenderSuzuki.FinalTheorem
import FeitThompson.FinalTheorem
import GorensteinWalter.FinalTheorem
import GorensteinWalter.GW1965
import GorensteinWalter.NormalPComplementQuotientPGroup
import GorensteinWalter.LinearRingEquiv
import GorensteinWalter.LinearThreeEquiv
import GorensteinWalter.PGL2CharacteristicSubgroup
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
import Mathlib.Tactic

noncomputable section

open Matrix
open GorensteinWalter
open Theory.Comparator
open scoped MatrixGroups

universe u

namespace CFSG

/-- **Feit--Thompson odd-order theorem.** -/
public theorem odd_order_theorem (G : Type u) [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) : Group.IsSolvable G :=
  _root_.odd_order_theorem G hodd

/-- **The Bender-Suzuki theorem.** -/
public theorem bender_suzuki {X : Type u} [Group X] [Finite X] [IsSimpleGroup X] (M : Subgroup X)
    (hM : IsStronglyEmbedded M) : IsSimpleBenderGroup X := by
  rcases _root_.bender_suzuki M hM with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · exact .isPSL2 n hn e
  · exact .isSuzuki n hn e
  · exact .isPSU3 n hn e

private theorem isPGroup_of_quotient_oddCore_of_oddCore_eq_bot
    {G : Type} [Group G] [Finite G]
    (hO : pPrimeCore 2 G = ⊥)
    (hQ : IsPGroup 2 (G ⧸ pPrimeCore 2 G)) :
    IsPGroup 2 G := by
  let e : G ≃* (G ⧸ pPrimeCore 2 G) :=
    ((QuotientGroup.quotientMulEquivOfEq (G := G) hO).trans
      (QuotientGroup.quotientBot (G := G))).symm
  exact hQ.of_equiv e.symm

private theorem not_isPGroup_two_of_nonabelian_simple
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) :
    ¬ IsPGroup 2 G := by
  intro hG
  let : Group.IsNilpotent G := hG.isNilpotent
  have hcomm : ∀ a b : G, a * b = b * a :=
    IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab (hcomm a b)

private theorem psl2_card_three_not_simple
    {G K : Type} [Group G] [Finite G] [IsSimpleGroup G]
    [Field K] [Finite K]
    (hKcard : Nat.card K = 3)
    (e : G ≃* PSL2 K) : False := by
  let : Fintype K := Fintype.ofFinite K
  have hFcard : Fintype.card K = 3 := by
    simpa [Nat.card_eq_fintype_card] using hKcard
  let eK : ZMod 3 ≃+* K :=
    ZMod.ringEquivOfPrime K Nat.prime_three hFcard
  let eA4 : G ≃* alternatingGroup (Fin 4) :=
    e.trans ((psl2RingEquiv eK).symm.trans
      psl2_three_equiv_alternatingGroup)
  let : IsSimpleGroup (alternatingGroup (Fin 4)) :=
    (MulEquiv.isSimpleGroup_congr eA4).mp inferInstance
  let V : Subgroup (alternatingGroup (Fin 4)) :=
    alternatingGroup.kleinFour (Fin 4)
  have hVnormal : V.Normal := by
    dsimp [V]
    exact alternatingGroup.normal_kleinFour (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal V hVnormal with hbot | htop
  · have hbad : (4 : ℕ) = 1 := by
      calc
        4 = Nat.card V := by
          symm
          exact alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
        _ = Nat.card (⊥ : Subgroup (alternatingGroup (Fin 4))) :=
          congrArg (fun H : Subgroup (alternatingGroup (Fin 4)) => Nat.card H) hbot
        _ = 1 := Subgroup.card_bot
    omega
  · have hbad : (4 : ℕ) = 12 := by
      calc
        4 = Nat.card V := by
          symm
          exact alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
        _ = Nat.card (⊤ : Subgroup (alternatingGroup (Fin 4))) :=
          congrArg (fun H : Subgroup (alternatingGroup (Fin 4)) => Nat.card H) htop
        _ = Nat.card (alternatingGroup (Fin 4)) := Subgroup.card_top
        _ = 12 := alternatingGroup.card_of_card_eq_four (by simp)
    omega

/-- **Gorenstein--Walter theorem.** -/
public theorem gorenstein_walter (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G)
    (_hdih : ∃ n : ℕ, Nonempty ((P : Subgroup G) ≃* DihedralGroup n)) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    ∃ p k : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
      Nonempty (G ≃* PSL(2, GaloisField p k)) := by
  obtain ⟨n, ⟨eP⟩⟩ := _hdih
  obtain ⟨r, hPcard⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hcard : 2 * n = 2 ^ r := by
    calc
      2 * n = Nat.card (DihedralGroup n) := DihedralGroup.nat_card.symm
      _ = Nat.card (P : Subgroup G) := (Nat.card_congr eP.toEquiv).symm
      _ = 2 ^ r := hPcard
  cases r with
  | zero => omega
  | succ m =>
      have hn : n = 2 ^ m := by
        rw [pow_succ] at hcard
        omega
      have htwoP : 2 ∣ Nat.card (P : Subgroup G) := by
        rw [hPcard, pow_succ]
        simp [mul_comm]
      have heven : 2 ∣ Nat.card G :=
        dvd_trans htwoP (Subgroup.card_subgroup_dvd_card (P : Subgroup G))
      have hO : pPrimeCore 2 G = ⊥ :=
        pPrimeCore_eq_bot_of_simple_of_even heven
      have hnotTwo : ¬ IsPGroup 2 G :=
        not_isPGroup_two_of_nonabelian_simple hnonab
      have hm : 1 ≤ m := by
        by_contra hm
        have hm0 : m = 0 := by omega
        subst m
        have hcyclic : HasCyclicSylowTwo G := by
          intro S
          apply isCyclic_of_prime_card (p := 2)
          calc
            Nat.card (S : Subgroup G) = Nat.card (P : Subgroup G) :=
              Nat.card_congr (Sylow.equiv S P).toEquiv
            _ = 2 := by simpa using hPcard
        have hNPC : Glauberman.NormalPComplement 2 G :=
          gw_prop9_burnside_cyclicSylowTwo_normalTwoComplement hcyclic
        have hQ : IsPGroup 2 (G ⧸ pPrimeCore 2 G) :=
          isPGroup_quotient_pPrimeCore_of_normalPComplement hNPC
        exact hnotTwo
          (isPGroup_of_quotient_oddCore_of_oddCore_eq_bot hO hQ)
      rw [hn] at eP
      have hdihedral : HasDihedralSylowTwo G := by
        intro S
        exact ⟨m, hm, ⟨(Sylow.equiv S P).trans eP⟩⟩
      have hD : IsDGroup G :=
        GorensteinWalter.gorenstein_walter G hdihedral
      let eQG : (G ⧸ pPrimeCore 2 G) ≃* G :=
        (QuotientGroup.quotientMulEquivOfEq (G := G) hO).trans
          (QuotientGroup.quotientBot (G := G))
      rcases hD with ⟨_hSylow, hQ⟩ | ⟨_hSylow, eA7⟩ |
          ⟨_hSylow, K, hKprimePower, L, hLnormal, hLindex, hLmodel⟩
      · exact False.elim (hnotTwo
          (isPGroup_of_quotient_oddCore_of_oddCore_eq_bot hO hQ))
      · exact Or.inl ⟨eQG.symm.trans eA7.some⟩
      · let : IsSimpleGroup (G ⧸ pPrimeCore 2 G) := eQG.isSimpleGroup
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L hLnormal with hLbot | hLtop
        · have hoddQ : Odd (Nat.card (G ⧸ pPrimeCore 2 G)) := by
            simpa [hLbot] using hLindex
          have hevenQ : Even (Nat.card (G ⧸ pPrimeCore 2 G)) := by
            rw [Nat.card_congr eQG.toEquiv]
            exact even_iff_two_dvd.mpr heven
          exact False.elim ((Nat.not_even_iff_odd.mpr hoddQ) hevenQ)
        · rw [hLtop] at hLmodel
          rcases hLmodel with hPSL | hPGL
          · let eGK : G ≃* PSL2 K :=
              eQG.symm.trans (Subgroup.topEquiv.symm.trans hPSL.some)
            rcases hKprimePower with ⟨p, k, hp, hpodd, hk, hKcard⟩
            have hpge : 3 ≤ p := by
              have hp2 : 2 ≤ p := hp.two_le
              have hpne : p ≠ 2 := by
                intro h
                subst p
                exact hpodd.not_two_dvd_nat (by simp)
              omega
            have hqge : 3 ≤ p ^ k := by
              calc
                3 ≤ p := hpge
                _ = p ^ 1 := by simp
                _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
            have hqne : p ^ k ≠ 3 := by
              intro hq
              apply psl2_card_three_not_simple (G := G) (K := K)
                (hKcard.trans hq) eGK
            have hqfive : 5 ≤ p ^ k := by
              have hqodd : Odd (p ^ k) := hpodd.pow
              rcases hqodd with ⟨a, ha⟩
              omega
            let : Fact p.Prime := ⟨hp⟩
            let : Fintype K := Fintype.ofFinite K
            have hKFcard : Fintype.card K = p ^ k := by
              simpa [Nat.card_eq_fintype_card] using hKcard
            let : CharP K p := charP_of_card_eq_prime_pow hKFcard
            let : Algebra (ZMod p) K := ZMod.algebra K p
            let eK : K ≃+* GaloisField p k :=
              (GaloisField.algEquivGaloisField p k hKcard).toRingEquiv
            exact Or.inr ⟨p, k, inferInstance, hpodd, hqfive,
              ⟨eGK.trans (psl2RingEquiv eK)⟩⟩
          · let eGPGL : G ≃* PGL2 K :=
              eQG.symm.trans (Subgroup.topEquiv.symm.trans hPGL.some)
            have hcomm :=
              commutator_ne_bot_ne_top_of_mulEquiv_pgl2_odd
                K hKprimePower eGPGL
            rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
                (commutator G) (inferInstance : (commutator G).Normal) with
              hbot | htop
            · exact False.elim (hcomm.1 hbot)
            · exact False.elim (hcomm.2 htop)

end CFSG
