module

public import Stellmacher.SectionFiveToSeven.PFamilyBridge
public import Stellmacher.SectionThree.LemmaThreeFour
public import Stellmacher.BaumannIntermediate
public import Stellmacher.BaumannNormalizer
public import Theory.GroupTheory.Commutator.TwoSubgroupNormalizer

/-!
# The two-residual has full Baumann commutator in Stellmacher (5.2)

For the solvable `P ∈ PStarFamily (C_H(Ω1(Z(S)))) S` of (5.2), a
nontrivial subgroup `K ≤ P` satisfying `[K,B(S)] = K` forces
`[O²(P),B(S)] = O²(P)`.  This is the property needed when the
maximal-counterexample argument replaces `K` by the larger subgroup `O²(P)`.

Lemma (3.4) gives the desired equality unless `B(S) ≤ O₂(P)`.  In that
exceptional case Baumann heredity identifies `B(S)` with `B(O₂(P))`, so
normality of `O₂(P)` makes `P` normalize `B(S)`.  The original commutator
equality then puts `K` inside the two-group `B(S)`.  Applied internally to
`B(S)`, the minimality theorem for a full commutator shows `K = 1`, contrary
to the hypothesis.

Source: B. Stellmacher, *An Application of the Amalgam Method: The 2-Local
Structure of N-Groups of Characteristic 2 Type*, Journal of Algebra 190
(1997), proof of (5.2), p. 28, together with Lemma (3.4).
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

open BenderSuzuki.External

universe u

private theorem le_normalizer_twoCoreIn_residualBaumann
    {G : Type u} [Group G] (P : Subgroup G) :
    P ≤ Subgroup.normalizer (twoCoreIn P : Set G) := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.map_subtype_le (pCore 2 P))).mp
  change (Subgroup.comap P.subtype ((pCore 2 P).map P.subtype)).Normal
  rw [Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  exact (inferInstance : (pCore 2 P).Normal)

private theorem sectionThreeHypotheses_of_pstar_residualBaumann
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (P : Subgroup G)
    (hP : P ∈ PStarFamily
      (Subgroup.centralizer (omegaOneCenter (S : Subgroup G) : Set G))
      (S : Subgroup G)) :
    Stellmacher.SectionThree.Hypotheses G (S : Subgroup G) := by
  have hcoreP_le_S : twoCoreIn P ≤ (S : Subgroup G) := by
    obtain ⟨_, T, hT⟩ := hP.1.1.2.1
    rw [← hT]
    exact Subgroup.map_mono
      ((pCore_isPGroup (G := P) (p := 2)).le_sylow_of_normal T)
  have hSne : (S : Subgroup G) ≠ ⊥ := by
    intro hbot
    exact hP.1.1.2.2.1
      (le_bot_iff.mp (hcoreP_le_S.trans (le_of_eq hbot)))
  let _ : Nontrivial (S : Subgroup G) :=
    (Subgroup.nontrivial_iff_ne_bot (S : Subgroup G)).2 hSne
  obtain ⟨n, hn, hcard⟩ := S.isPGroup'.nontrivial_iff_card.mp inferInstance
  have heven : Even (Nat.card G) := by
    apply even_iff_two_dvd.mpr
    apply (show 2 ∣ Nat.card (S : Subgroup G) by
      rw [hcard]
      exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)).trans
    exact Subgroup.card_subgroup_dvd_card (S : Subgroup G)
  exact ⟨heven, hSne, S.isPGroup'⟩

/-- A nontrivial full Baumann commutator forces the same commutator equality
for the two-residual of its local-family member. -/
public theorem five_two_residual_baumann_commutator
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (P K : Subgroup G)
    (hP : P ∈ PStarFamily
      (Subgroup.centralizer (omegaOneCenter (S : Subgroup G) : Set G))
      (S : Subgroup G))
    (hsolv : Group.IsSolvable P)
    (hK : K ≤ P)
    (hcomm : K = ⁅K, baumannIn (S : Subgroup G)⁆)
    (hKne : K ≠ ⊥) :
    ⁅twoResidualIn P, baumannIn (S : Subgroup G)⁆ = twoResidualIn P := by
  let S0 : Subgroup G := (S : Subgroup G)
  let B : Subgroup G := baumannIn S0
  let O : Subgroup G := twoCoreIn P
  let R : Subgroup G := twoResidualIn P
  have hSP : S0 ≤ P := hP.1.1.2.1.1
  have hOS : O ≤ S0 := by
    obtain ⟨_, T, hT⟩ := hP.1.1.2.1
    change twoCoreIn P ≤ (S : Subgroup G)
    rw [← hT]
    simpa [twoCoreIn] using Subgroup.map_mono (f := P.subtype)
      ((pCore_isPGroup (G := P) (p := 2)).le_sylow_of_normal T)
  have hBS : B ≤ S0 := inf_le_left
  have hBnormalS : (B.subgroupOf S0).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hBS).mpr
    exact S0.le_normalizer.trans (by
      simpa [B, baumannIn, omegaOneCenter,
        Stellmacher.omegaOneCenterAmbient] using
        (Stellmacher.normalizer_le_normalizer_baumann S0))
  have hthree := sectionThreeHypotheses_of_pstar_residualBaumann S P hP
  have hPset : P ∈ Stellmacher.SectionThree.PSet (⊤ : Subgroup G) S0 := by
    rw [← pFamily_iff_pSet]
    exact ⟨⟨le_top, hP.1.1.2⟩, hP.1.2⟩
  rcases Stellmacher.SectionThree.lemma_three_four S0 hthree P hPset B
      ⟨hBS, hBnormalS⟩ hsolv with hBO | hRB
  · exfalso
    have hBeq :
        O ⊓ Subgroup.centralizer
          (Stellmacher.omegaOneCenterAmbient
            (Stellmacher.elementaryAbelianMaxJ O) : Set G) = B := by
      simpa [B, O, baumannIn, omegaOneCenter,
        Stellmacher.omegaOneCenterAmbient] using
        (Stellmacher.baumann_eq_of_intermediate S0 O (by
          simpa [B, baumannIn, omegaOneCenter,
            Stellmacher.omegaOneCenterAmbient, O, twoCoreIn,
            Stellmacher.twoCoreAmbient] using hBO) hOS)
    have hPnormB : P ≤ Subgroup.normalizer (B : Set G) := by
      have hPnormO : P ≤ Subgroup.normalizer (O : Set G) :=
        le_normalizer_twoCoreIn_residualBaumann P
      have hnorm := hPnormO.trans
        (Stellmacher.normalizer_le_normalizer_baumann O)
      rw [hBeq] at hnorm
      exact hnorm
    have hKnormB : K ≤ Subgroup.normalizer (B : Set G) := hK.trans hPnormB
    have hKleB : K ≤ B := by
      rw [hcomm]
      exact Subgroup.le_normalizer_iff_commutator_le_right.mp hKnormB
    let KB : Subgroup B := K.subgroupOf B
    have hmapKB : KB.map B.subtype = K :=
      Subgroup.map_subgroupOf_eq_of_le hKleB
    have hmapTop : (⊤ : Subgroup B).map B.subtype = B := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hcommB : ⁅KB, (⊤ : Subgroup B)⁆ = KB := by
      apply Subgroup.map_injective B.subtype_injective
      rw [Subgroup.map_commutator, hmapKB, hmapTop, ← hcomm]
    let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hBp : IsPGroup 2 B := S.isPGroup'.to_le hBS
    have hquot : IsPGroup 2 (B ⧸ (⊥ : Subgroup B)) :=
      hBp.to_quotient (⊥ : Subgroup B)
    have hKBbot : KB ≤ (⊥ : Subgroup B) :=
      Subgroup.le_normal_of_quotient_isPGroup_of_eq_commutator
        KB ⊤ ⊥ hquot hcommB
    apply hKne
    apply le_antisymm
    · intro k hk
      have hkB : ⟨k, hKleB hk⟩ ∈ KB := hk
      have hkOne : (⟨k, hKleB hk⟩ : B) = 1 := hKBbot hkB
      exact congrArg Subtype.val hkOne
    · exact bot_le
  · change ⁅Stellmacher.twoResidualAmbient P, B⁆ =
      Stellmacher.twoResidualAmbient P
    exact hRB

end Stellmacher.SectionsFiveToSeven
