module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualCatalogueSquare
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CentralIntersectionRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RankOneCentralEquivalences
public import Theory.SpecificGroups.Suzuki.TwoRank

/-!
# DGS 8.6 for every nonlinear beta quotient

If the moving center is not natural, the first comparison makes the full
opposite actor have order at least four. The nonlinear residual square bound
therefore applies to its escaping moving center. The two opposite quotient
omega parameters agree by actual graph conjugation, so the two comparisons
contradict each other. The small rank-one terminal models use the direct
rank-one comparison. Thus every nonlinear catalogue row gives naturality at
the starting vertex and identifies H with the terminal center.

Source: DGS, Groups and Graphs (1985), 8.6, printed pp.139--140.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph CommutingTrivial
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

private theorem nonlinear_comparison
    (h : HypothesisF11 L S₀)
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
    (hinter : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1 ⊓ Q (Reduction.reducedFamily L S₀) beta⁆ = ⊥)
    {n : ℕ} (hn : 0 < n)
    (hr : primeRank 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≤ n)
    (hlower : 4 ≤ (Q (Reduction.reducedFamily L S₀) beta).relIndex
      (V (Reduction.reducedFamily L S₀) a' 1) →
      ∀ E : Subgroup (Reduction.G₀ L S₀), E ≤ V (Reduction.reducedFamily L S₀) a' 1 →
      ¬ E ≤ Q (Reduction.reducedFamily L S₀) beta →
      (2^n)^2 ≤ (centralizer (E : Set (Reduction.G₀ L S₀))).relIndex
        (V (Reduction.reducedFamily L S₀) beta 1)) :
    Noncommuting.HasNaturalCenter (graphLocalGroup (Reduction.reducedFamily L S₀) w.val)
      (Z (Reduction.reducedFamily L S₀) w.val) (Q (Reduction.reducedFamily L S₀) w.val) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let R : Sylow 2 (graphLocalGroup Γ w.val) := default
  let T : Sylow 2 (graphLocalGroup Γ a') := default
  let U : Sylow 2 (graphLocalGroup Γ beta) := default
  let : Finite (graphLocalGroup Γ beta) := Finite.of_injective
    (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite (graphLocalGroup Γ a') := Finite.of_injective
    (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite (graphLocalGroup Γ w.val) := Finite.of_injective
    (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let Uq := U.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 (graphLocalGroup Γ beta)))
  let Tq := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 (graphLocalGroup Γ a')))
  have hU : Nat.card (omegaCenterIn Uq.toSubgroup) ≤ 2^n :=
    (primeRank_le_iff_elementary_card_le _).mp hr _ inferInstance
  obtain ⟨_,_,_,_,_,_,hparameters⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
  have hT : Nat.card (omegaCenterIn Tq.toSubgroup) ≤ 2^n := (hparameters Tq Uq).le.trans hU
  rcases source_moving_omega_square_or_natural ht (Reduction.reduced_borel_core_sylow h)
    d models hc hab hd hb hcomm w hm R with hnat | hs
  · exact hnat
  exfalso
  let A := V Γ beta 1 ⊓ Q Γ a'
  have hb3 : 3 ≤ b Γ := (source_critical_geometry ht d hc hab hd hb hcomm).2.1
  let : IsElementaryAbelian 2 (V Γ beta 1) := V_elementary Γ ht.generate
    (fun v => (source_Z_Q_U ht v).1) (Reduction.reduced_kernel_sylow h) beta (by omega)
  let : IsElementaryAbelian 2 (V Γ a' 1) := V_elementary Γ ht.generate
    (fun v => (source_Z_Q_U ht v).1) (Reduction.reduced_kernel_sylow h) a' (by omega)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  have hAL : A ≤ d.localGroup w.val := (source_moving_actor ht d hc hab hd hb hcomm w hm).2.1
  have hAQ : ¬ A ≤ Q Γ w.val := (source_moving_actor ht d hc hab hd hb hcomm w hm).2.2.2.1
  let : Finite (d.localGroup w.val) := Finite.of_injective
    (inclusion (d.local_le w.val)) (inclusion_injective _)
  let : Finite A := Finite.of_injective (inclusion hAL) (inclusion_injective _)
  have hidx2 : 2 ≤ (Q Γ w.val).relIndex A := by
    have h0 := ((Q Γ w.val).subgroupOf A).index_ne_zero_of_finite
    have h1 : (Q Γ w.val).relIndex A ≠ 1 := fun he => hAQ (relIndex_eq_one.mp he)
    change (Q Γ w.val).relIndex A ≠ 0 at h0
    omega
  have hR2 := hidx2.trans (source_elementary_core_index_le_omega ht d w.val (models w.val) A hAL R)
  have hs' := hs.trans (source_commuting_intersection_fixed_index_le ht hb w hinter)
  let qR := Nat.card (omegaCenterIn ((R : Subgroup (graphLocalGroup Γ w.val)).map
    (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ w.val)))))
  change 2 ≤ qR at hR2
  change qR^2 ≤ (Q Γ beta).relIndex (V Γ a' 1) at hs'
  have hlarge : 4 ≤ (Q Γ beta).relIndex (V Γ a' 1) := by nlinarith only [hR2,hs']
  have hVL : V Γ a' 1 ≤ d.localGroup beta := neighbor_le_graphLocalGroup ht
    (Reduction.reduced_kernel_sylow h) a' beta hb (by
      change (graph Γ).dist a' beta + 1 ≤ b Γ
      rw [SimpleGraph.dist_comm]
      exact hd.le)
  have hsmall := hs'.trans ((source_elementary_core_index_le_omega ht d beta (models beta)
    (V Γ a' 1) hVL U).trans hU)
  have hEQ : ¬ Z Γ w.val ≤ Q Γ beta := by
    intro hZ
    exact hm (bot_unique ((commutator_mono le_rfl
      (le_inf (Z_neighbor_le_V Γ w.property) hZ)).trans hinter.le))
  have hlo := hlower hlarge (Z Γ w.val) (Z_neighbor_le_V Γ w.property) hEQ
  have hup := source_opposite_centralizer_index_le_omega_product ht
    (Reduction.reduced_borel_core_sylow h) d models hc hab hd hb hcomm w hm R T
  have hmul := Nat.mul_le_mul_right (Nat.card (omegaCenterIn ((R : Subgroup
    (graphLocalGroup Γ w.val)).map (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ w.val)))))) hT
  have hprod := hlo.trans (hup.trans hmul)
  have hpos : 1 < 2^n := Nat.one_lt_pow (by omega) (by decide)
  change qR^2 ≤ 2^n at hsmall
  change (2^n)^2 ≤ 2^n*qR at hprod
  nlinarith only [hsmall,hprod,hpos]

/-- All nonlinear catalogue rows discharge DGS 8.6(c) ⇒ (d), with the
literal original commutator and no residual-action or size premise. -/
theorem reduced_nonlinear_terminal_commuting_intersection_natural
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ ≠ ⊥)
    (hnonlinear : ∀ n : ℕ, 0 < n → ¬ ClassicalGroup.IsPSL
      (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) 2 (2^n))
    (hinter : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1 ⊓ Q (Reduction.reducedFamily L S₀) beta⁆ = ⊥) :
    let Γ := Reduction.reducedFamily L S₀
    Noncommuting.HasNaturalCenter (graphLocalGroup Γ a) (Z Γ a) (Q Γ a) ∧
      ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ = Z Γ a' := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let : Finite (graphLocalGroup Γ beta) := Finite.of_injective
    (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite (graphLocalGroup Γ a') := Finite.of_injective
    (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  obtain ⟨w,hm,_⟩ := exists_moving_neighbor Γ (fun v => (source_Z_Q_U ht v).1) beta a' hne
  obtain ⟨_,_,e,_,_,_,_⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
  have hsmall (hr : primeRank 2 (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≤ 1) :
      Noncommuting.HasNaturalCenter (graphLocalGroup Γ a) (Z Γ a) (Q Γ a) := by
    have hr' : primeRank 2 (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a')) ≤ 1 := by
      rwa [primeRank_congr 2 e]
    exact (reduced_rank_one_terminal_intersection_natural h models hc hab hd hb hcomm hne hr' hinter).2.2
  have htransport (hnat : Noncommuting.HasNaturalCenter (graphLocalGroup Γ w.val) (Z Γ w.val) (Q Γ w.val)) :
      Noncommuting.HasNaturalCenter (graphLocalGroup Γ a) (Z Γ a) (Q Γ a) := by
    have hodd : Odd ((graph Γ).dist a a') := by
      rw [hc.1]
      exact (source_critical_geometry ht d hc hab hd hb hcomm).1
    have hna : a.type ≠ a'.type := (odd_dist_iff Γ ht.generate a a').mp hodd
    have hnw : a'.type ≠ w.val.type := w.property.1
    have hwa : w.val.type = a.type :=
      (Bool.eq_not_of_ne hnw.symm).trans (Bool.eq_not_of_ne hna).symm
    exact source_natural_center_of_type ht d hwa hnat
  have hnat : Noncommuting.HasNaturalCenter (graphLocalGroup Γ a) (Z Γ a) (Q Γ a) := by
    cases models beta with
    | linear n hn hi => exact (hnonlinear n hn hi).elim
    | suzuki m hi =>
      let eβ := hi.some
      have hr : primeRank 2 (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≤ 2*m+1 := by
        rw [primeRank_congr 2 eβ]
        by_cases hm : m = 0
        · subst m
          let R := zpowers suzukiZeroRootGenerator
          have hcR : Nat.card R = 2^2 := by rw [Nat.card_zpowers,suzukiZeroRootGenerator_order]; rfl
          have hp : IsPGroup 2 R := IsPGroup.of_card hcR
          have hiR : ¬ 2 ∣ R.index := by
            have he := R.card_mul_index
            rw [show Nat.card R = 4 from hcR,suzukiZero_card] at he
            have hx : R.index = 5 := by omega
            simp only [hx]
            decide
          apply (hp.toSylow hiR).primeRank_le_one_of_isCyclic
          change IsCyclic R
          infer_instance
        · exact (suzuki_two_rank m (by omega)).le
      apply htransport
      apply nonlinear_comparison h models hc hab hd hb hcomm w hm hinter (by omega : 0 < 2*m+1) hr
      intro _ E hEV hEQ
      exact reduced_critical_suzuki_residual_square h hc hab hd hb hcomm m eβ E hEV hEQ
    | dihedral hi =>
      apply hsmall
      rw [primeRank_congr 2 hi.some]
      let S : Sylow 2 (DihedralGroup 5) := Sylow.ofCard
        (zpowers (DihedralGroup.sr 0 : DihedralGroup 5)) (by
          rw [Nat.card_zpowers,DihedralGroup.orderOf_sr,DihedralGroup.nat_card]
          rw [Nat.factorization_mul (by decide) (by decide),
            Nat.prime_two.factorization,Nat.prime_five.factorization]
          norm_num)
      exact S.primeRank_le_one_of_isCyclic
        (inferInstanceAs (IsCyclic (zpowers (DihedralGroup.sr 0 : DihedralGroup 5))))
    | projective_unitary n hn hi =>
      obtain ⟨K,_,_,J,hK,hconj,⟨eβ⟩⟩ := hi
      let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
        Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
      have hr : primeRank 2 (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≤ n := by
        rw [primeRank_congr 2 eβ]
        exact (HermitianForm.EvenTwoRank.two_rank J hn hK hconj).le
      by_cases hn2 : 2 ≤ n
      · apply htransport
        apply nonlinear_comparison h models hc hab hd hb hcomm w hm hinter hn hr
        intro hlarge E hEV hEQ
        exact reduced_critical_unitary_residual_square h hc hab hd hb hcomm hn2
          (Or.inl ⟨K,inferInstance,inferInstance,J,hK,hconj,⟨eβ⟩⟩) hlarge E hEV hEQ
      · apply hsmall
        exact hr.trans (by omega)
    | special_unitary n hn hi =>
      obtain ⟨K,_,_,J,hK,hconj,⟨eβ⟩⟩ := hi
      let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
        Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
      have hr : primeRank 2 (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≤ n := by
        rw [primeRank_congr 2 eβ,primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
          J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
        exact (HermitianForm.EvenTwoRank.two_rank J hn hK hconj).le
      by_cases hn2 : 2 ≤ n
      · apply htransport
        apply nonlinear_comparison h models hc hab hd hb hcomm w hm hinter hn hr
        intro hlarge E hEV hEQ
        exact reduced_critical_unitary_residual_square h hc hab hd hb hcomm hn2
          (Or.inr ⟨K,inferInstance,inferInstance,J,hK,hconj,⟨eβ⟩⟩) hlarge E hEV hEQ
      · apply hsmall
        exact hr.trans (by omega)
  exact ⟨hnat,source_natural_center_commutator_eq_terminal ht
    (Reduction.reduced_borel_core_sylow h) d hc hab hd hb hcomm hne hnat⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
