module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.BinaryUnitaryCentrality.TerminalCatalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CentralEquivalencesSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualNaturalitySource

/-!
# Small terminal quotients in the binary unitary moving branch

At critical distance three, the middle local group exchanges beta and
alpha-prime. Translate the entire original critical configuration by that
element, including its nonzero displacement. Source 8.5 then excludes a
natural residual section at alpha-prime. For a linear terminal field of
order at least four, the residual square bound applied to the original
Z_alpha contradicts the binary upper bound q_beta * 2.

Together with the unitary and Suzuki exclusions in `TerminalCatalogue`,
this leaves PSL₂(2), D₁₀, Sz(2), PSU₃(2), and SU₃(2) as terminal models.
Their actual Sylows give two-rank at most one. Criticality and the graph
exchange force both opposite actor indices to equal two, so the original
starting-center fixed index on V_alpha-prime is at most four. Criticality
also shows that Z_alpha supplements V_beta intersect Q_alpha-prime in V_beta.

These statements retain the chosen moving neighbor, its nonzero commutator,
both binary unitary covers, and the literal graph and quotient maps. They
reduce the remaining centrality proof to the small terminal configurations;
they do not assert the fixed-subgroup escape or the conclusion of 8.7.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
8.1, 8.5--8.7, printed pp.132--140, in particular the residual square
comparison on p.140. The exchange retains the residual at its own vertex.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial.BinaryUnitaryCentrality
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "Γ" => Reduction.reducedFamily J S₀

/-- No linear terminal field of order at least four occurs with the
original binary unitary moving neighbor. The exchanged original branch
supplies the terminal residual exclusion without an additional premise. -/
theorem reduced_large_linear_terminal_impossible
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) 3 2 ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 2)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2^n)
    (e : (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a')) ≃* SL(2,K)) : False := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hne : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ ≠ ⊥ := by
    intro hz
    exact hm (bot_unique ((commutator_mono le_rfl (Z_neighbor_le_V Γ w.property)).trans hz.le))
  have hb3 := reduced_distance_three_of_catalogue h models hc hab hd hb hcomm hne
  obtain ⟨_,_,_,_,mid,ham,hdm,_,_⟩ := source_critical_geometry ht d hc hab hd hb hcomm
  change (graph Γ).dist beta mid + 1 = (graph Γ).dist beta a' at hdm
  change (graph Γ).Adj a' mid at ham
  have hbm : (graph Γ).Adj beta mid := SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
  obtain ⟨g,_,hgb,hga⟩ := source_rank_one_neighbor_exchange ht
    (Reduction.reduced_borel_core_sylow h) d hbm.symm ham.symm (models mid)
  change g • beta = a' at hgb
  change g • a' = beta at hga
  obtain ⟨hc',hcomm',hne'⟩ := branch_translate Γ hc hcomm hne g
  rw [hgb,hga] at hne'
  rw [hga] at hc' hcomm'
  have hab' : (graph Γ).Adj (g • a) a' := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso Γ g).map_adj_iff.mpr hab
    change (graph Γ).Adj (g • a) (g • beta) at hh
    rwa [hgb] at hh
  have hd' : (graph Γ).dist a' beta + 1 = b Γ := by rwa [SimpleGraph.dist_comm]
  have hinterval := reduced_critical_linear_paired_intervals h models hc' hab' hd' hb hcomm' hne' e
  have hnot := reduced_natural_residual_exclusion_of_catalogue h models hc' hab' hd' hb hcomm' hne'
    (by omega : 0 < n) hK e
  have hZa : ¬ Z Γ a ≤ Q Γ a' := fun he => hc.2 (he.trans (source_Z_Q_U ht a').2)
  have hlo := reduced_critical_nonnatural_residual_square h hc' hab' hd' hb hcomm'
    (Reduction.reduced_graph_core_obstruction h (g • a) a' hab') (by omega : 1 < n) hK e
    hinterval.2.1 (Z Γ a) (Z_neighbor_le_V Γ hab.symm) hZa hnot
  have hupper := reduced_terminal_fixed_index_le_twice h models hc hab hd hb hcomm w hm hu
  have heq := reduced_critical_paired_core_indices_eq h models hc hab hd hb hcomm hne
  rw [←heq,hinterval.2.1] at hupper
  have hbound := hlo.trans hupper
  have hfour : 4 ≤ Nat.card K := hK.symm ▸ Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) hn
  nlinarith

/-- The terminal catalogue is small, including both unitary covers. -/
theorem reduced_small_terminal_catalogue
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) 3 2 ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 2)
    : let D := graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a')
      ClassicalGroup.IsPSL D 2 2 ∨ Nonempty (D ≃* DihedralGroup 5) ∨
        Nonempty (D ≃* SuzukiMatrixGroup 0) ∨ ClassicalGroup.IsPSU D 3 2 ∨ IsSU D 3 2 := by
  rcases reduced_terminal_catalogue h models hc hab hd hb hcomm w hm hu with hl | hs
  · obtain ⟨n,hn,hlin⟩ := hl
    by_cases hn2 : 2 ≤ n
    · obtain ⟨K,_,_,hK,⟨eK⟩⟩ := hlin
      let := Fintype.ofFinite K
      let : CharP K 2 := charP_of_card_eq_prime_pow
        (by simpa only [Nat.card_eq_fintype_card] using hK)
      let e := eK.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
        ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
      exact (reduced_large_linear_terminal_impossible h models hc hab hd hb hcomm w hm hu hn2 hK e).elim
    · have hn1 : n = 1 := by omega
      exact Or.inl (by simpa only [hn1,pow_one] using hlin)
  · exact Or.inr hs

private theorem small_terminal_two_rank {D : Type*} [Group D] [Finite D]
    (hsmall : ClassicalGroup.IsPSL D 2 2 ∨ Nonempty (D ≃* DihedralGroup 5) ∨ Nonempty (D ≃* SuzukiMatrixGroup 0) ∨
      ClassicalGroup.IsPSU D 3 2 ∨ IsSU D 3 2) : primeRank 2 D ≤ 1 := by
  rcases hsmall with hlin | hsmall
  · obtain ⟨K,_,_,hK,⟨eK⟩⟩ := hlin
    let := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
      (by simpa only [pow_one,Nat.card_eq_fintype_card] using hK)
    let e : D ≃* SL(2,K) := eK.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
    rw [primeRank_congr 2 e]
    let S : Sylow 2 SL(2,K) := default
    have hc : Nat.card S = 2 := by
      rw [←Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive K 2 S).toEquiv]
      exact hK
    exact S.primeRank_le_one_of_isCyclic (isCyclic_of_prime_card hc)
  ·
    rcases hsmall with hlin | hsuz | hpsu | hsu
    · obtain ⟨e⟩ := hlin
      rw [primeRank_congr 2 e]
      let S : Sylow 2 (DihedralGroup 5) := Sylow.ofCard
        (zpowers (DihedralGroup.sr 0 : DihedralGroup 5)) (by
          rw [Nat.card_zpowers,DihedralGroup.orderOf_sr,DihedralGroup.nat_card]
          rw [Nat.factorization_mul (by decide) (by decide),
            Nat.prime_two.factorization,Nat.prime_five.factorization]
          norm_num)
      exact S.primeRank_le_one_of_isCyclic
        (inferInstanceAs (IsCyclic (zpowers (DihedralGroup.sr 0 : DihedralGroup 5))))
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

/-- The binary moving marking forces terminal two-rank at most one. -/
theorem reduced_terminal_rank_one
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) 3 2 ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 2)
    : primeRank 2 (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a')) ≤ 1 := by
  let : ∀ i, Finite (Γ i) := finite_endpoints (Reduction.reduced_triple h)
  let : Finite (graphLocalGroup Γ a') :=
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  exact small_terminal_two_rank (reduced_small_terminal_catalogue h models hc hab hd hb hcomm w hm hu)

/-- Both original opposite actor indices are exactly two. The original
starting-center fixed index on the terminal span is at most four. -/
theorem reduced_binary_indices
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) 3 2 ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 2)
    : (Q Γ a').relIndex (V Γ beta 1) = 2 ∧
      (Q Γ beta).relIndex (V Γ a' 1) = 2 ∧
      (centralizer (Z Γ a : Set (Reduction.G₀ J S₀))).relIndex (V Γ a' 1) ≤ 4 := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hne : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ ≠ ⊥ := by
    intro hz
    exact hm (bot_unique ((commutator_mono le_rfl (Z_neighbor_le_V Γ w.property)).trans hz.le))
  have hr := reduced_terminal_rank_one h models hc hab hd hb hcomm w hm hu
  have hi := source_ending_rank_actor_bounds ht d hc hab hd hb hcomm 1 hr
  have hx : (Q Γ a').relIndex (V Γ beta 1) = 2 := by
    have hVL : V Γ beta 1 ≤ stabilizer Γ beta :=
      V_le_stabilizer_of_dist_add_le_b Γ ht.generate beta beta 1 (by
        simpa only [SimpleGraph.dist_self,zero_add] using hb.le)
    let : Finite (V Γ beta 1) := Finite.of_injective (inclusion hVL) (inclusion_injective _)
    have h0 : (Q Γ a').relIndex (V Γ beta 1) ≠ 0 :=
      ((Q Γ a').subgroupOf (V Γ beta 1)).index_ne_zero_of_finite
    have h1 : (Q Γ a').relIndex (V Γ beta 1) ≠ 1 := by
      intro he
      exact hc.2 ((Z_neighbor_le_V Γ hab.symm).trans
        ((relIndex_eq_one.mp he).trans (source_Z_Q_U ht a').2))
    have hh := hi.1
    change (Q Γ a').relIndex (V Γ beta 1) ≤ 2^1 at hh
    norm_num only [pow_one] at hh
    omega
  have hy : (Q Γ beta).relIndex (V Γ a' 1) = 2 :=
    (reduced_critical_paired_core_indices_eq h models hc hab hd hb hcomm hne).symm.trans hx
  refine ⟨hx,hy,?_⟩
  have hh := reduced_terminal_fixed_index_le_twice h models hc hab hd hb hcomm w hm hu
  simpa only [hy] using hh

/-- The actual starting center supplements the terminal-core intersection
inside the beta span; the quotient has order two and criticality supplies
its nonzero image. -/
theorem reduced_starting_center_supplement
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) 3 2 ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 2)
    : Z Γ a ⊔ (V Γ beta 1 ⊓ Q Γ a') = V Γ beta 1 := by
  let ht := Reduction.reduced_triple h
  let A := V Γ beta 1 ⊓ Q Γ a'
  let D := Z Γ a ⊔ A
  have hZV : Z Γ a ≤ V Γ beta 1 := Z_neighbor_le_V Γ hab.symm
  have hDV : D ≤ V Γ beta 1 := sup_le hZV inf_le_left
  have hi : A.relIndex (V Γ beta 1) = 2 := by
    rw [inf_relIndex_left]
    exact (reduced_binary_indices h models hc hab hd hb hcomm w hm hu).1
  have h1 : A.relIndex D ≠ 1 := by
    intro he
    exact hc.2 ((show Z Γ a ≤ D from le_sup_left).trans
      ((relIndex_eq_one.mp he).trans (inf_le_right.trans (source_Z_Q_U ht a').2)))
  have he := relIndex_mul_relIndex A D (V Γ beta 1) le_sup_right hDV
  rw [hi] at he
  have hD : D.relIndex (V Γ beta 1) = 1 := by
    rcases Nat.prime_mul_iff.mp (he ▸ Nat.prime_two) with hp | hp
    · exact hp.2
    · exact (h1 hp.2).elim
  exact le_antisymm hDV (relIndex_eq_one.mp hD)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial.BinaryUnitaryCentrality
