module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RadiusThreeFixedIndex

/-!
# Distance restrictions for the selected terminal models

For a linear terminal quotient at any positive binary degree, and for
D₁₀, Sz(2), PSU₃(2) or SU₃(2), the radius-three residual contradiction
excludes b >= 7. Source parity leaves exactly b = 3 or b = 5. If the
moving quotient is linear or D₁₀, its elementary Sylow image also supplies
the intersection placement at b = 5, giving b = 3.

The last theorem constructs the moving neighbor and its actual edge Sylow,
and transports an original linear or D₁₀ starting quotient to that neighbor.
Thus its only extra premises are the stated actual endpoint model cases;
no moving-neighbor, placement, fixed-index or distance callback remains.
All applications use an arbitrary ordered critical pair on the reduced
F1.11 graph. Nonlinear b = 5 placement, large nonlinear terminal residual
bounds, and the later 8.5--8.7 conclusions remain separate source obligations.

Source: DGS, *Groups and Graphs* (1985), 8.1(a), 8.4(3) and its final
paragraph, pp.132,138. The small model ranks use their literal Sylow groups
and the odd scalar kernel of the full special unitary cover.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

private theorem small_ending_rank {D : Type*} [Group D] [Finite D]
    (hsmall : Nonempty (D ≃* DihedralGroup 5) ∨ Nonempty (D ≃* SuzukiMatrixGroup 0) ∨
      ClassicalGroup.IsPSU D 3 2 ∨ IsSU D 3 2) : primeRank 2 D ≤ 1 := by
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

/-- Actual linear and small terminal markings discharge the numerical
premises of the radius-three residual contradiction. -/
theorem reduced_radius_three_selected_contradiction
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 3 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val))
    (hR : (R : Subgroup (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)).map
      (graphLocalGroup (Reduction.reducedFamily J S₀) w.val).subtype =
      (stabilizer (Reduction.reducedFamily J S₀) w.val ⊓
        stabilizer (Reduction.reducedFamily J S₀) a').pCoreIn 2)
    (hcase : 6 < b (Reduction.reducedFamily J S₀) ∨
      (∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL
        (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
          pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) 2 (2 ^ n)) ∨
      Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) ≃* DihedralGroup 5))
    (hend : (∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL
      (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) 2 (2^n)) ∨
      Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≃* DihedralGroup 5) ∨
      Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≃* SuzukiMatrixGroup 0) ∨
      ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) 3 2 ∨ IsSU (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) 3 2) : False := by
  rcases hend with hlin | hr
  · obtain ⟨n,hn,K,_,_,hK,⟨eK⟩⟩ := hlin
    let := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hK)
    let e := eK.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
    exact reduced_radius_three_linear_contradiction h hob models hc hab hd hb hcomm
      w hm R hR hcase hn hK e
  · let ht := Reduction.reduced_triple h
    let d := Reduction.reducedEarlierLocalTheorems h hob
    let : ∀ i, Finite (Reduction.reducedFamily J S₀ i) := finite_endpoints ht
    let : Finite (d.localGroup a') :=
      Finite.of_injective (inclusion (d.local_le a')) (inclusion_injective _)
    have hr' : primeRank 2 (d.localGroup a' ⧸ pCore 2 (d.localGroup a')) ≤ 1 :=
      small_ending_rank hr
    exact reduced_radius_three_rank_one_contradiction h hob models hc hab hd hb hcomm
      w hm R hR hcase hr'

/-- For every linear or small terminal model, only critical distances
three and five remain. The moving neighbor and edge Sylow are constructed. -/
theorem reduced_selected_ending_distance_le_five
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    (hend : (∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL
      (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) 2 (2^n)) ∨
      Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≃* DihedralGroup 5) ∨
      Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≃* SuzukiMatrixGroup 0) ∨
      ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) 3 2 ∨ IsSU (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) 3 2) :
    b (Reduction.reducedFamily J S₀) = 3 ∨ b (Reduction.reducedFamily J S₀) = 5 := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  obtain ⟨hodd,hb3,_⟩ := source_critical_geometry ht d hc hab hd hb hcomm
  change Odd (b F) at hodd
  change 3 ≤ b F at hb3
  have hle : b F ≤ 5 := by
    by_contra! hh
    have hb7 : 6 < b F := by obtain ⟨k,hk⟩ := hodd; change b F = 2*k+1 at hk; omega
    obtain ⟨w,hm,_⟩ := exists_moving_neighbor F (fun v => (source_Z_Q_U ht v).1) beta a' hne
    obtain ⟨R,hR⟩ := source_edge_core_local_sylow ht (Reduction.reduced_borel_core_sylow h)
      d w.property.symm
    exact reduced_radius_three_selected_contradiction h hob models hc hab hd (by change 3 < b F; omega) hcomm
      w hm R hR (Or.inl hb7) hend
  obtain ⟨k,hk⟩ := hodd
  change b F = 2*k+1 at hk
  change b F = 3 ∨ b F = 5
  omega

/-- An elementary moving quotient closes the remaining b = 5 case for
the selected terminal models. -/
theorem reduced_selected_ending_distance_three
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val))
    (hR : (R : Subgroup (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)).map
      (graphLocalGroup (Reduction.reducedFamily J S₀) w.val).subtype =
      (stabilizer (Reduction.reducedFamily J S₀) w.val ⊓
        stabilizer (Reduction.reducedFamily J S₀) a').pCoreIn 2)
    (hshape : (∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL
        (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
          pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) 2 (2 ^ n)) ∨
      Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) ≃* DihedralGroup 5))
    (hend : (∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL
      (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) 2 (2^n)) ∨
      Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≃* DihedralGroup 5) ∨
      Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≃* SuzukiMatrixGroup 0) ∨
      ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) 3 2 ∨ IsSU (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) 3 2) : b (Reduction.reducedFamily J S₀) = 3 := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedEarlierLocalTheorems h hob
  have hb3 := (source_critical_geometry ht d hc hab hd hb hcomm).2.1
  change 3 ≤ b (Reduction.reducedFamily J S₀) at hb3
  by_contra he
  have hb' : 3 < b (Reduction.reducedFamily J S₀) := by omega
  exact reduced_radius_three_selected_contradiction h hob models hc hab hd hb' hcomm
    w hm R hR (Or.inr hshape) hend

/-- The starting model marking transports to the constructed moving
neighbor. This gives b = 3 from the original critical configuration and
the specified actual endpoint models, in either orientation. -/
theorem reduced_selected_models_distance_three
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    (hend : (∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL
      (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) 2 (2^n)) ∨
      Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≃* DihedralGroup 5) ∨
      Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≃* SuzukiMatrixGroup 0) ∨
      ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) 3 2 ∨ IsSU (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) 3 2)
    (hstart : (∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL
      (graphLocalGroup (Reduction.reducedFamily J S₀) a ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a)) 2 (2^n)) ∨
      Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) a ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a)) ≃* DihedralGroup 5)) : b (Reduction.reducedFamily J S₀) = 3 := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let : ∀ i, Finite (F i) := finite_endpoints ht
  have hodd := (source_critical_geometry ht d hc hab hd hb hcomm).1
  have hod : Odd ((graph F).dist a a') := hc.1.symm ▸ hodd
  have htypes := (odd_dist_iff F ht.generate a a').mp hod
  obtain ⟨w,hm,_⟩ := exists_moving_neighbor F (fun v => (source_Z_Q_U ht v).1) beta a' hne
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow ht (Reduction.reduced_borel_core_sylow h)
    d w.property.symm
  have htype : a.type = w.val.type := by
    have hw := w.property.1
    generalize a.type = x at htypes ⊢
    generalize a'.type = y at htypes hw
    generalize w.val.type = z at hw ⊢
    cases x <;> cases y <;> cases z <;> tauto
  obtain ⟨g,hg⟩ := (same_orbit_iff F a w.val).mpr htype
  have heq : d.localGroup w.val = (d.localGroup a).map (MulAut.conj g).toMonoidHom := by
    rw [←hg,d.conjugate]
  let f := (MulEquiv.subgroupCongr heq).trans
    ((d.localGroup a).equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
  let e := QuotientGroup.congr _ _ f (pCore_map_iso 2 f)
  have hshape : (∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL
      (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) 2 (2^n)) ∨
      Nonempty ((d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* DihedralGroup 5) := by
    rcases hstart with hlin | hdih
    · obtain ⟨n,hn,K,_,_,hK,⟨eK⟩⟩ := hlin
      exact Or.inl ⟨n,hn,K,inferInstance,inferInstance,hK,⟨e.trans eK⟩⟩
    · obtain ⟨eK⟩ := hdih
      exact Or.inr ⟨e.trans eK⟩
  exact reduced_selected_ending_distance_three h hob models hc hab hd hb hcomm w hm R hR hshape hend

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
