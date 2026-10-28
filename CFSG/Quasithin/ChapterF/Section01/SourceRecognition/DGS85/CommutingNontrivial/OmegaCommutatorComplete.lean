module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.EndingCatalogueCommutator
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LinearReversePaired

/-!
# The complete nontrivial commuting quotient-omega inclusion, DGS 8.3

All ending rows of the actual source quotient catalogue are discharged.
For a large linear ending, the original failure provides a uniformly
nonnatural residual action; the reverse estimate uses a translated critical
configuration on that same action. Every other ending row is already closed
by the paired constituent estimates or the binary rank bound.

This constructs the moving neighbor and its full-edge Sylow on the reduced
F1.11 graph. The genuine earlier 6.5 obstruction and quotient catalogue are
retained for final source assembly. The distance-three and later module
conclusions of 8.4–8.7 are separate obligations.

Source: DGS85, Groups and Graphs, (8.3), printed pp.135–137.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

private theorem binary_ending_rank {D : Type*} [Group D] [Finite D]
    (hsmall : ClassicalGroup.IsPSL D 2 2 ∨ Nonempty (D ≃* SuzukiMatrixGroup 0) ∨
      ClassicalGroup.IsPSU D 3 2 ∨ IsSU D 3 2) : primeRank 2 D ≤ 1 := by
  rcases hsmall with hlin | hsuz | hpsu | hsu
  · obtain ⟨K,_,_,hK,⟨eK⟩⟩ := hlin
    let := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
      (by simpa only [pow_one,Nat.card_eq_fintype_card] using hK)
    let e := eK.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
    rw [primeRank_congr 2 e]
    let T : Sylow 2 SL(2,K) := default
    rw [T.primeRank_eq]
    apply (primeRank_le_iff_elementary_card_le T).mpr
    intro E _
    have hc : Nat.card T = Nat.card K :=
      (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive K 2 T).toEquiv).symm
    exact (Subgroup.card_le_card_group E).trans (by simpa only [pow_one,hK] using hc.le)
  · obtain ⟨e⟩ := hsuz
    rw [primeRank_congr 2 e]
    let R := zpowers suzukiZeroRootGenerator
    have hc : Nat.card R = 2^2 := by
      rw [Nat.card_zpowers,suzukiZeroRootGenerator_order]
      rfl
    have hp : IsPGroup 2 R := IsPGroup.of_card hc
    have hi : ¬ 2 ∣ R.index := by
      have he := R.card_mul_index
      rw [show Nat.card R = 4 from hc,suzukiZero_card] at he
      have hx : R.index = 5 := by omega
      simp only [hx]
      decide
    apply (hp.toSylow hi).primeRank_le_one_of_isCyclic
    change IsCyclic R
    infer_instance
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hpsu
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    rw [primeRank_congr 2 e]
    exact (HermitianForm.EvenTwoRank.two_rank J (n := 1) (by decide) hK hconj).le
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hsu
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    rw [primeRank_congr 2 e,primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
      J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
    exact (HermitianForm.EvenTwoRank.two_rank J (n := 1) (by decide) hK hconj).le

/-- The original 8.3 inclusion at every specified moving neighbor and its
full-edge Sylow, with the complete actual quotient catalogue discharged. -/
theorem reduced_moving_omega_commutator
    (h : HypothesisF11 L S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily L S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      Z (Reduction.reducedFamily L S₀) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily L S₀) w.val))
    (hR : (R : Subgroup (graphLocalGroup (Reduction.reducedFamily L S₀) w.val)).map
      (graphLocalGroup (Reduction.reducedFamily L S₀) w.val).subtype =
        (stabilizer (Reduction.reducedFamily L S₀) w.val ⊓ stabilizer (Reduction.reducedFamily L S₀) a').pCoreIn 2)
 :
    ⁅quotientSylowOmegaPreimage (graphLocalGroup (Reduction.reducedFamily L S₀) w.val) R,
      Z (Reduction.reducedFamily L S₀) w.val⁆ ≤
        ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
          V (Reduction.reducedFamily L S₀) a' 1⁆ := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily L S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : Finite (graphLocalGroup F a') :=
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hsmall (hr : primeRank 2 (graphLocalGroup F a' ⧸ pCore 2 (graphLocalGroup F a')) ≤ 1) :
      ⁅quotientSylowOmegaPreimage (graphLocalGroup F w.val) R,Z F w.val⁆ ≤
        ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ :=
    source_ending_two_rank_one_omega_commutator ht (Reduction.reduced_borel_core_sylow h)
      d hc hab hd hb hcomm models w hm R hR hr
  cases models a' with
  | linear n hn hi =>
      by_cases hn2 : 2 ≤ n
      · obtain ⟨K,_,_,hK,⟨eK⟩⟩ := hi
        let := Fintype.ofFinite K
        let : CharP K 2 := charP_of_card_eq_prime_pow
          (by simpa only [Nat.card_eq_fintype_card] using hK)
        let e := eK.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
          ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
        exact reduced_linear_moving_omega_commutator h hob models hc hab hd hb hcomm w hm R hR hn2 hK e
      · have hn1 : n = 1 := by omega
        exact hsmall (binary_ending_rank (Or.inl (by simpa only [hn1,pow_one] using hi)))
  | suzuki k hi =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact hsmall (binary_ending_rank (Or.inr (Or.inl hi)))
      · exact reduced_suzuki_moving_omega_commutator h hob models hc hab hd hb hcomm w hm R hR k hk hi.some
  | projective_unitary n hn hi =>
      by_cases hn2 : 2 ≤ n
      · exact reduced_unitary_moving_omega_commutator h hob models hc hab hd hb hcomm w hm R hR n hn2 (Or.inl hi)
      · have hn1 : n = 1 := by omega
        exact hsmall (binary_ending_rank (Or.inr (Or.inr (Or.inl (by simpa only [hn1,pow_one] using hi)))))
  | special_unitary n hn hi =>
      by_cases hn2 : 2 ≤ n
      · exact reduced_unitary_moving_omega_commutator h hob models hc hab hd hb hcomm w hm R hR n hn2 (Or.inr hi)
      · have hn1 : n = 1 := by omega
        exact hsmall (binary_ending_rank (Or.inr (Or.inr (Or.inr (by simpa only [hn1,pow_one] using hi)))))
  | dihedral hi =>
      apply hsmall
      rw [primeRank_congr 2 hi.some]
      let S : Sylow 2 (DihedralGroup 5) := Sylow.ofCard (zpowers (DihedralGroup.sr 0 : DihedralGroup 5)) (by
        rw [Nat.card_zpowers,DihedralGroup.orderOf_sr,DihedralGroup.nat_card]
        rw [Nat.factorization_mul (by decide) (by decide),
          Nat.prime_two.factorization,Nat.prime_five.factorization]
        norm_num)
      exact S.primeRank_le_one_of_isCyclic
        (inferInstanceAs (IsCyclic (zpowers (DihedralGroup.sr 0 : DihedralGroup 5))))

/-- DGS 8.3 on the literal nontrivial commuting source branch, with no
paired-index, reverse-failure, naturality or model-row premise left over. -/
theorem reduced_omega_commutator
    (h : HypothesisF11 L S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓
      Q (Reduction.reducedFamily L S₀) a',V (Reduction.reducedFamily L S₀) a' 1⁆ ≠ ⊥) :
    let F := Reduction.reducedFamily L S₀
    ¬ V F a' 1 ≤ Q F beta ∧
      ∃ w : (graph F).neighborSet a',
        ⁅V F beta 1 ⊓ Q F a',Z F w.val⁆ ≠ ⊥ ∧
        ∃ R : Sylow 2 (graphLocalGroup F w.val),
          (R : Subgroup (graphLocalGroup F w.val)).map (graphLocalGroup F w.val).subtype =
            (stabilizer F w.val ⊓ stabilizer F a').pCoreIn 2 ∧
          ⁅quotientSylowOmegaPreimage (graphLocalGroup F w.val) R,Z F w.val⁆ ≤
            ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily L S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  have he := reduced_reciprocal_escape h hob models hc hab hd hb hcomm hne
  obtain ⟨w,hm,_⟩ := exists_moving_neighbor F (fun v => (source_Z_Q_U ht v).1) beta a' hne
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow ht (Reduction.reduced_borel_core_sylow h) d w.property.symm
  exact ⟨he,w,hm,R,hR,reduced_moving_omega_commutator h hob models hc hab hd hb hcomm w hm R hR⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
