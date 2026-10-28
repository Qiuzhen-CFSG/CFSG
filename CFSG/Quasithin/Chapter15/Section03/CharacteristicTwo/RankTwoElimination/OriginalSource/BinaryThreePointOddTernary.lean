module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeExtensionProjectiveModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeExtensionCovers
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.OddThree
public import Theory.GroupTheory.PerfectRankTwoCoreInvolution
public import Theory.GroupTheory.PCoreSectionCard
public import Theory.SpecificGroups.SL2.LinearThreeSection
public import Theory.SpecificGroups.PSL3.DefiningRank
public import Theory.SpecificGroups.OddThreeSylowOrder
public import Theory.SpecificGroups.OddThreeSevenResidual

/-!
# Odd ternary exclusion from the original binary-three join

The actual join B⋁T has two-core quotient of order dividing 168. Restrict
its intersection to a containing C-component K, preserving the full
relative Sylow and the original B/O₂(B)≃PSL₃(2). If B has trivial two-core,
odd ternary faithfulness kills the intersection's two-core, contradicting
its full Sylow order. Otherwise a central involution and the actual cubic
central covering embed B into prime-field SL₂. Its original quotient
forces characteristic seven and B≃SL₂(7).

The exact linear and unitary ternary-seven centralizer bounds then exclude
an overgroup with two-core quotient dividing 168. In particular the
projective linear argument keeps its cubic scalar quotient; no surviving
scalar C₃ is assumed. Both signs and special/projective carriers remain.
The generic calculations adapt PointOddTernary and PointTernaryExclusion
in Chapter12; no Chapter12 source geometry is imported as a premise.
Source: Aschbacher--Smith A.3.21(a), p.55, and 12.5.3, pp.817--818,
applied to the original 15.3.23 join, pp.1128--1129.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open Chapter1.Section02.LocalModels ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open Theory.SpecificGroups.OddThreeSevenResidual

private theorem odd_ternary_sixteen {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : IsPSLSign Q u 3 p ∨ IsSLSign Q u 3 p) : 16 ∣ Nat.card Q := by
  cases u
  · rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
    · rw [Nat.card_congr e.toEquiv]
      exact Theory.SpecificGroups.OddThreeSylowOrder.projective_sixteen_dvd_card (hF.symm ▸ ho)
    · rw [Nat.card_congr e.toEquiv]
      exact Theory.SpecificGroups.OddThreeSylowOrder.special_sixteen_dvd_card (hF.symm ▸ ho)
  · rcases hm with ⟨F,_,_,J,hF,hc,⟨e⟩⟩ | ⟨F,_,_,J,hF,hc,⟨e⟩⟩
    · rw [Nat.card_congr e.toEquiv]
      exact Theory.SpecificGroups.OddThreeSylowOrder.unitary_projective_sixteen_dvd_card J hp ho hF hc
    · rw [Nat.card_congr e.toEquiv]
      exact Theory.SpecificGroups.OddThreeSylowOrder.unitary_special_sixteen_dvd_card J hp ho hF hc

private theorem core_eq_bot_of_normal_corefree_faithful {Q : Type*} [Group Q] [Finite Q]
    (S : Sylow 2 Q) (B J : Subgroup Q) (hBJ : B ≤ J)
    (hn : J ≤ normalizer (B : Set Q)) (hSJ : (S : Subgroup Q) ≤ J)
    (hB : pCore 2 B = ⊥) (hf : (S : Subgroup Q) ⊓ centralizer (B : Set Q) = ⊥) :
    pCore 2 J = ⊥ := by
  have hnC : J ≤ normalizer (J.pCoreIn 2 : Set Q) := by
    simpa only [pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using (pCore 2 J).le_normalizer_map J.subtype
  have hcomm : ⁅J.pCoreIn 2,B⁆ ≤ B.pCoreIn 2 := by
    apply le_trans _ (inf_pCoreIn_le_of_le 2 hBJ)
    refine le_inf ?_ ?_
    · exact le_normalizer_iff_commutator_le_right.mp ((pCoreIn_le 2 J).trans hn)
    · rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_right.mp (hBJ.trans hnC)
  have hc : J.pCoreIn 2 ≤ centralizer (B : Set Q) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    simpa only [pCoreIn,hB,Subgroup.map_bot] using hcomm
  have hs : J.pCoreIn 2 ≤ (S : Subgroup Q) := by
    have hh := (pCore_isPGroup (p := 2) (G := J)).le_sylow_of_normal (S.subtype hSJ)
    have hm := map_mono (f := J.subtype) hh
    simpa only [pCoreIn,Sylow.coe_subtype,map_subgroupOf_eq_of_le hSJ] using hm
  exact ((pCore 2 J).map_eq_bot_iff_of_injective J.subtype_injective).mp
    (bot_unique ((le_inf hs hc).trans hf.le))

private theorem signed_ternary_no_small_quotient
    {Q : Type*} [Group Q] [Finite Q] (S : Sylow 2 Q) (B J : Subgroup Q)
    (e : B ≃* SL(2,ZMod 7)) (hBJ : B ≤ J) (hn : J ≤ normalizer (B : Set Q))
    (hSJ : (S : Subgroup Q) ≤ J) (unitary : Bool)
    (hm : IsPSLSign Q unitary 3 7 ∨ IsSLSign Q unitary 3 7) :
    ¬ Nat.card (J ⧸ pCore 2 J) ∣ 168 := by
  have transport {H : Type} [Group H] [Finite H] (a : Q ≃* H)
      (h : ∀ (S : Sylow 2 H) (B J : Subgroup H),
        (B ≃* SL(2,ZMod 7)) → B ≤ J → J ≤ normalizer (B : Set H) →
        (S : Subgroup H) ≤ J → ¬ Nat.card (J ⧸ pCore 2 J) ∣ 168) :
      ¬ Nat.card (J ⧸ pCore 2 J) ∣ 168 := by
    intro hsmall
    let b := B.equivMapOfInjective a.toMonoidHom a.injective
    let j := J.equivMapOfInjective a.toMonoidHom a.injective
    apply h (S.mapSurjective a.surjective) (B.map a.toMonoidHom) (J.map a.toMonoidHom)
      (b.symm.trans e) (map_mono hBJ)
      ((map_mono hn).trans (B.le_normalizer_map a.toMonoidHom)) (map_mono hSJ)
    rwa [←Nat.card_congr (QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).toEquiv]
  cases unitary
  · rcases hm with ⟨F,_,_,hF,⟨a⟩⟩ | ⟨F,_,_,hF,⟨a⟩⟩
    · exact transport a (projective_linear_no_small_quotient hF)
    · exact transport a (special_linear_no_small_quotient hF)
  · rcases hm with ⟨F,_,_,M,hF,hc,⟨a⟩⟩ | ⟨F,_,_,M,hF,hc,⟨a⟩⟩
    · let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup M) :=
        Finite.of_surjective a a.surjective
      exact transport a (projective_unitary_no_small_quotient M hF hc)
    · exact transport a (special_unitary_no_small_quotient M hF hc)

private theorem binary_three_odd_ternary_core_ne_bot
    {Q : Type*} [Group Q] [Finite Q] (S : Sylow 2 Q) (B J : Subgroup Q)
    [Group.IsPerfect B] (hBJ : B ≤ J) (hn : J ≤ normalizer (B : Set Q))
    (hSJ : (S : Subgroup Q) ≤ J) (eB : (B ⧸ pCore 2 B) ≃* SL(3,ZMod 2))
    (hsmall : Nat.card (J ⧸ pCore 2 J) ∣ 168)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hm : IsPSLSign Q unitary 3 p ∨ IsSLSign Q unitary 3 p) :
    pCore 2 B ≠ ⊥ := by
  intro hcore
  let e : B ≃* SL(3,ZMod 2) := ((QuotientGroup.quotientBot.symm).trans
    (QuotientGroup.quotientMulEquivOfEq hcore.symm)).trans eB
  have hz : center B = ⊥ := by
    apply eq_bot_iff.mpr
    intro b hb
    have hh : e b ∈ center SL(3,ZMod 2) := (centerCongr e ⟨b,hb⟩).property
    rw [BinaryLinear.OuterCyclic.binary_center_eq_bot (by decide : 0 < 3),mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hr : 2 ≤ primeRank 2 B := by
    rw [primeRank_congr 2 e]
    rw [primeRank_congr 2 Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two]
    exact Matrix.PSL3.DefiningRank.two_mul_fieldExponent_le_primeRank (ZMod 2) (e := 1) (by simp)
  have hf := ChapterC.Section05.NormalizerControl.EmbeddingSelection.odd_three_perfect_sylow_faithful
    S B hz hr hp ho unitary hm
  have hJ := core_eq_bot_of_normal_corefree_faithful S B J hBJ hn hSJ hcore hf
  have hc : Nat.card J ∣ 168 := by
    rwa [hJ,Nat.card_congr (QuotientGroup.quotientBot (G := J)).toEquiv] at hsmall
  have h16 : 16 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 4)
    (odd_ternary_sixteen hp ho unitary hm)
  have hd := (h16.trans (card_dvd_of_le hSJ)).trans hc
  norm_num at hd

private theorem binary_three_odd_ternary_residual_model
    {Q : Type*} [Group Q] [Finite Q] (S : Sylow 2 Q) (B J : Subgroup Q)
    [Group.IsPerfect B] (hBJ : B ≤ J) (hn : J ≤ normalizer (B : Set Q))
    (hSJ : (S : Subgroup Q) ≤ J) (eB : (B ⧸ pCore 2 B) ≃* SL(3,ZMod 2))
    (hsmall : Nat.card (J ⧸ pCore 2 J) ∣ 168)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hm : IsPSLSign Q unitary 3 p ∨ IsSLSign Q unitary 3 p) :
    p = 7 ∧ Nonempty (B ≃* SL(2,ZMod p)) := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsSimpleGroup SL(3,ZMod 2) := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup (B ⧸ pCore 2 B) := eB.isSimpleGroup
  let : Nontrivial B := (QuotientGroup.mk'_surjective (pCore 2 B)).nontrivial
  obtain ⟨z,_,hz,hzB⟩ := exists_involution_centralized_by_perfect_sup_sylow S B
    (odd_three_two_rank ho unitary hm) (hSJ.trans hn)
    (binary_three_odd_ternary_core_ne_bot S B J hBJ hn hSJ eB hsmall hp ho unitary hm)
  obtain ⟨r,H,_,_,hH,f,hf,hc,h3⟩ := odd_three_cubic_carrier ho unitary hm
  obtain ⟨i,hi⟩ := rankThree_cubic_quotient_perfect_embedding
    hH f hf hc h3 z hz B (le_sup_left.trans hzB)
  have hp3 : 3 < p := by
    by_contra hh
    have he : p = 3 := by have := hp.two_le; have := Nat.odd_iff.mp ho; omega
    have hsol : Group.IsSolvable SL(2,ZMod 3) := by
      let : Group.IsSolvable (GL (Fin 2) (ZMod 3)) := Matrix.GeneralLinearGroup.three_isSolvable
      exact Group.isSolvable_of_isSolvable_injective
        (Matrix.SpecialLinearGroup.toGL_injective (n := Fin 2) (R := ZMod 3))
    let : Group.IsSolvable SL(2,ZMod p) := he ▸ hsol
    exact Group.IsPerfect.not_isSolvable B (Group.isSolvable_of_isSolvable_injective hi)
  let : Group.IsSolvable i.ker := by
    rw [(MonoidHom.ker_eq_bot_iff i).mpr hi]
    infer_instance
  obtain ⟨hp7,hproj⟩ := Theory.SL2.prime_seven_and_projective_surjective_of_solvable_kernel
    ((Nat.card_congr eB.toEquiv).trans Atlas.Comparisons.Exceptional.sl3Two_card)
    hp hp3 (Nat.card_zmod p) i
  let : Group.IsPerfect SL(2,ZMod p) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three (ZMod p) (by simpa using hp3)
  have hsurj : Function.Surjective i :=
    PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      (QuotientGroup.mk' (center SL(2,ZMod p))) i hproj (by rw [QuotientGroup.ker_mk'])
  exact ⟨hp7,⟨MulEquiv.ofBijective i ⟨hi,hsurj⟩⟩⟩

/-- The original quotient and a normalizing full-Sylow overgroup with
two-core quotient dividing 168 exclude every odd prime ternary carrier. -/
theorem binary_three_not_odd_ternary_of_small_normalizing_quotient
    {Q : Type*} [Group Q] [Finite Q] (S : Sylow 2 Q) (B J : Subgroup Q)
    [Group.IsPerfect B] (hBJ : B ≤ J) (hn : J ≤ normalizer (B : Set Q))
    (hSJ : (S : Subgroup Q) ≤ J) (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (hsmall : Nat.card (J ⧸ pCore 2 J) ∣ 168)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hm : IsPSLSign Q unitary 3 p ∨ IsSLSign Q unitary 3 p) : False := by
  obtain ⟨rfl,⟨e⟩⟩ := binary_three_odd_ternary_residual_model S B J hBJ hn hSJ
    (eB.trans Matrix.PSL3Two.equiv.symm) hsmall hp ho unitary hm
  exact signed_ternary_no_small_quotient S B J e hBJ hn hSJ unitary hm hsmall

/-- Restrict the actual B⋁T to the containing C-component. Its original
order-168 quotient excludes all odd ternary models for that same K. -/
theorem binary_three_point_not_odd_ternary
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (hjoin : Nat.card ((B ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (B ⊔ (T : Subgroup G) : Subgroup G)) ∣ 168)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hm : IsPSLSign K unitary 3 p ∨ IsSLSign K unitary 3 p) : False := by
  obtain ⟨S,hS,hl⟩ := exists_local_sylow_restriction T hB hBK hK.subnormal
  let A := B.subgroupOf K
  let J := B ⊔ (T : Subgroup G)
  let I := J.subgroupOf K
  let a := subgroupOfEquivOfLe hBK
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let : Group.IsPerfect A := by
    let := hl.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show A ≤ A ⊔ (S : Subgroup K) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  have hAI : A ≤ I := comap_mono (show B ≤ J from le_sup_left)
  have hn : I ≤ normalizer (A : Set K) := by
    rw [←subgroupOf_normalizer_eq hBK]
    exact comap_mono (sup_le B.le_normalizer hTB)
  have hSI : (S : Subgroup K) ≤ I := by
    rw [hS]
    exact comap_mono (show (T : Subgroup G) ≤ J from le_sup_right)
  let j : I →* J := K.subtype.subgroupComap J
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : J => (z : G)) he))
  have hsmall : Nat.card (I ⧸ pCore 2 I) ∣ 168 :=
    (MonoidHom.card_corefree_quotient_dvd_of_embedding j hj
      (QuotientGroup.mk' (pCore 2 I)) (QuotientGroup.mk'_surjective _)
      (pCore_quotient_pCore_eq_bot 2)).trans hjoin
  exact binary_three_not_odd_ternary_of_small_normalizing_quotient
    S A I hAI hn hSI (aq.trans eB) hsmall hp ho unitary hm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource

