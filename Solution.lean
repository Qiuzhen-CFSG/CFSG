module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Sylow
public import BenderSuzuki.FinalTheorem
import GorensteinWalter.FinalTheorem
public import Stellmacher.Recognition.FinalTheorem
public import Stellmacher.Recognition.MinimalSimpleFinalTheorem
public import Stellmacher.Recognition.PSL3ThreeModel
public import Stellmacher.Recognition.PSU3ThreeModel

noncomputable section

open Matrix
open GorensteinWalter
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

/-- `PSU₃(3)`, independently specified as the projective image of determinant-one
isometries over `GF(9)`, with identity Gram matrix and conjugation `x ↦ x³`. -/
@[expose] public noncomputable def PSU3ThreeModel :
    Subgroup (ProjGenLinGroup (Fin 3) (GaloisField 3 2)) :=
  (Subgroup.closure
    {A : GL (Fin 3) (GaloisField 3 2) |
      (Matrix.of fun i j => (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 2)) j i ^ 3)
          * (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 2)) = 1
        ∧ GeneralLinearGroup.det A = 1}).map ProjGenLinGroup.mk

private theorem psu3ThreeModel_eq : PSU3ThreeModel = ABG.PSU3 3 1 (by decide) := by
  have hset :
      {A : GL (Fin 3) (GaloisField 3 2) |
        (Matrix.of fun i j => (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 2)) j i ^ 3)
            * (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 2)) = 1
          ∧ GeneralLinearGroup.det A = 1} =
      ((ABG.unitaryForm 3 3 1 (by decide)).specialSubgroup : Set _) := by
    ext A
    change (_ ∧ _) ↔
      ((Matrix.of fun i j => (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 2)) j i ^ 3)
          * 1 * (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 2)) = 1 ∧ _)
    rw [mul_one]
    rfl
  unfold PSU3ThreeModel
  rw [hset, Subgroup.closure_eq]

/-- **Thompson's classification of minimal finite simple groups**, in both
directions. The hypotheses and all five model families are explicit.

Source: Thompson, *Nonsolvable finite groups all of whose local subgroups are
solvable*, I (1968), Corollary 1, p. 388. -/
public theorem minimal_simple_classification (G : Type u) [Group G] [Finite G] :
    (IsSimpleGroup G ∧ ¬ Group.IsSolvable G ∧
      ∀ H : Subgroup G, H < ⊤ → Group.IsSolvable H) ↔
    (∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* PSL(2, GaloisField 2 p))) ∨
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ Nonempty (G ≃* PSL(2, GaloisField 3 p))) ∨
    (∃ p : ℕ, ∃ _hp : Fact p.Prime, 3 < p ∧ (p % 5 = 2 ∨ p % 5 = 3) ∧
      Nonempty (G ≃* PSL(2, ZMod p))) ∨
    (∃ n : ℕ, (2 * n + 1).Prime ∧ Nonempty (G ≃* SzModel n)) ∨
    Nonempty (G ≃* PSL(3, ZMod 3)) := by
  constructor
  · rintro ⟨hs, hns, hproper⟩
    rcases Stellmacher.Recognition.isMinimalSimple_iff_thompsonModel.mp
        ⟨hs, hns, hproper⟩ with
      ⟨p, hp, e⟩ | ⟨p, hp, hodd, e⟩ | ⟨p, hp, hgt, hmod, e⟩ |
      ⟨n, hp, e⟩ | ⟨e⟩
    · exact .inl ⟨p, hp, ⟨e⟩⟩
    · exact .inr (.inl ⟨p, hp, hodd, ⟨e⟩⟩)
    · exact .inr (.inr (.inl ⟨p, ⟨hp⟩, hgt, hmod, ⟨e⟩⟩))
    · exact .inr (.inr (.inr (.inl ⟨n, hp, ⟨e⟩⟩)))
    · exact .inr (.inr (.inr (.inr ⟨e⟩)))
  · intro h
    suffices hG : IsMinimalSimple G from
      ⟨hG.isSimpleGroup, hG.not_isSolvable, hG.solvable_of_lt⟩
    apply Stellmacher.Recognition.isMinimalSimple_iff_thompsonModel.mpr
    rcases h with ⟨p, hp, ⟨e⟩⟩ | ⟨p, hp, hodd, ⟨e⟩⟩ |
      ⟨p, hp, hgt, hmod, ⟨e⟩⟩ | ⟨n, hp, ⟨e⟩⟩ | ⟨e⟩
    · exact .psl2Binary p hp e
    · exact .psl2ThreePower p hp hodd e
    · exact .psl2Prime p hp.out hgt hmod e
    · exact .suzuki n hp e
    · exact .psl3Three e.some

/-- **The classification of finite nonsolvable simple N₂ groups.** The N₂
hypothesis says explicitly that normalizers of nontrivial 2-subgroups are
solvable. Each alternative supplies an isomorphism with an actual group.

Sources: Kurzweil–Stellmacher, Appendix p. 370; Thompson VI (1974), p. 573
for the Tits correction. `Tits.ParrottGroup` is the ten-generator,
37-relator presentation from Parrott (1972), p. 683; `Sporadic.Mathieu.M11`
is the automorphism group of the explicit Witt `S(4,5,11)` design. -/
public theorem nTwo_classification (G : Type u) [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (hlocal : ∀ Q : Subgroup G, Q ≠ ⊥ → IsPGroup 2 Q →
      Group.IsSolvable (Subgroup.normalizer (Q : Set G))) :
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (G ≃* PSL(2, GaloisField 2 n))) ∨
    (∃ (K : Type u) (_ : Field K) (_ : Finite K),
      Odd (Nat.card K) ∧ 3 < Nat.card K ∧ Nonempty (G ≃* PSL(2, K))) ∨
    (∃ n : ℕ, 1 ≤ n ∧ Nonempty (G ≃* SzModel n)) ∨
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (G ≃* Sporadic.Mathieu.M11) ∨
    Nonempty (G ≃* PSL(3, ZMod 3)) ∨
    Nonempty (G ≃* PSU3ThreeModel) ∨
    Nonempty (G ≃* Tits.ParrottGroup) ∨
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (G ≃* PSU3Model n)) := by
  have hN : Stellmacher.IsNTwoGroup G := by
    rintro U ⟨Q, hQ, htwo, rfl⟩
    exact hlocal Q hQ htwo
  rcases Stellmacher.nTwo_classification hns hN with hmodel | hunitary
  · cases hmodel with
    | psl2Even n hn e => exact .inl ⟨n, hn, ⟨e⟩⟩
    | psl2Odd K hodd hcard e =>
      exact .inr (.inl ⟨K, inferInstance, inferInstance, hodd, hcard, ⟨e⟩⟩)
    | suzuki n hn e => exact .inr (.inr (.inl ⟨n, hn, ⟨e⟩⟩))
    | alternatingSeven e => exact .inr (.inr (.inr (.inl ⟨e⟩)))
    | mathieuEleven e => exact .inr (.inr (.inr (.inr (.inl ⟨e⟩))))
    | linearThree h =>
      exact .inr (.inr (.inr (.inr (.inr (.inl
        (ABG.isPSL3_three_iff_nonempty_mulEquiv.mp h))))))
    | unitaryThree h =>
      have he : Nonempty (G ≃* PSU3ThreeModel) := by
        rw [psu3ThreeModel_eq]
        exact ABG.isPSU3_three_iff_nonempty_mulEquiv.mp h
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inl he))))))
    | tits e => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨e⟩)))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr hunitary)))))))

end CFSG
