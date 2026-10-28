module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RadiusThreeDistance
public import Theory.Representation.SU3.TwoGroupFixedIndex
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RadiusThreeSuzuki

/-!
# The complete terminal catalogue in the DGS 8.4 residual argument

The original reciprocal elementary span escapes Q_beta. On the actual
residually moved W/V_beta, a special or projective unitary marking forces
fixed index at least the fixed-field order. The full neighboring-span
commutator and strict denominator bound contradict this after transporting
the terminal marking to beta by graph conjugation.

Combining these unitary cases with the linear, Suzuki and small models
excludes every critical distance at least seven. Source parity leaves
b=3 or b=5. A linear or D₁₀ starting marking supplies intersection placement
also at b=5, so the distance is three for every terminal model in that case.
These applications construct their moving neighbor and full-edge Sylow;
only the original earlier-source obstruction and actual catalogue remain
as inputs. The nonlinear b=5 intersection and 8.5--8.7 remain open.

Source: DGS, *Groups and Graphs* (1985), 5.7, 8.2 and 8.4, pp.108,134--138.
Every conclusion uses an arbitrary ordered critical pair in the reduced
F1.11 graph, preserving the original core and residual quotient conventions.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The literal residual denominator has index at least the beta unitary
fixed-field order in every established intersection branch. -/
theorem reduced_radius_three_unitary_fixed_index
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
    {K : Type*} [Field K] [Finite K] (H : HermitianForm 3 K)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, H.conj x = x^(2^n))
    (e : Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) beta)) ≃* H.specialSubgroup) ∨
      Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) beta)) ≃*
        ProjectiveSpecialUnitaryMatrixGroup H)) :
    let F := Reduction.reducedFamily J S₀
    2^n ≤ ((V F beta 3 ⊓ Q F a') ⊔ V F beta 1).relIndex (V F beta 3) := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let W := V F beta 3
  let V₀ := V F beta 1
  let I := W ⊓ Q F a'
  let D := I ⊔ V₀
  let A := V F a' 1
  let L := graphLocalGroup F beta
  let : ∀ i, Finite (F i) := finite_endpoints ht
  change 3 < b F at hb
  have hWP : W ≤ stabilizer F beta := V_le_stabilizer_of_dist_add_le_b F ht.generate
    beta beta 3 (by simpa using hb.le)
  let : Finite W := Finite.of_injective (inclusion hWP) (inclusion_injective _)
  have hVW : V₀ ≤ W := V_mono F beta (by decide)
  have hnV : W ≤ normalizer (V₀ : Set (Reduction.G₀ J S₀)) :=
    hWP.trans (stabilizer_normalizes_V F beta 1)
  have hnA : A ≤ normalizer (V₀ : Set (Reduction.G₀ J S₀)) :=
    (radius_one_mutual_normalization F ht.generate beta a' hd.le).2
  have hH : ⁅V₀ ⊓ Q F a',A⁆ ≤ V₀ :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hnA)
  have hI : ⁅I,A⁆ ≤ V₀ :=
    (reduced_radius_three_full_span_bound h hob models hc hab hd hb hcomm w hm R hR hcase).trans hH
  have hD : ⁅A,D⁆ ≤ V₀ := by
    rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal W I V₀ A V₀ hnV inf_le_left hVW hI
      (le_normalizer_iff_commutator_le_left.mp hnA)
  have hne : ⁅V₀ ⊓ Q F a',A⁆ ≠ ⊥ := by
    intro hz
    exact hm (bot_unique ((commutator_mono le_rfl (Z_neighbor_le_V F w.property)).trans hz.le))
  let : Finite L := Finite.of_injective (inclusion (d.local_le beta)) (inclusion_injective _)
  have hpW : IsPGroup 2 W := (isPGroup_pCoreIn 2 (stabilizer F beta)).to_le
    (V_le_Q_of_dist_add_lt_b F ht.generate (fun v => (source_Z_Q_U ht v).1)
      beta beta 3 (by simpa only [SimpleGraph.dist_self,zero_add] using hb) (d.kernel_sylow beta))
  have hAp : IsPGroup 2 A := (isPGroup_pCoreIn 2 (stabilizer F a')).to_le
    (V_le_Q_of_dist_add_lt_b F ht.generate (fun v => (source_Z_Q_U ht v).1)
      a' a' 1 (by simp only [SimpleGraph.dist_self,zero_add]; omega) (d.kernel_sylow a'))
  have hAP : A ≤ stabilizer F beta := V_le_stabilizer_of_dist_add_le_b F ht.generate
    a' beta 1 (by rw [SimpleGraph.dist_comm]; exact hd.le)
  have hAL : A ≤ L := pGroup_le_localGroup F d beta A hAp hAP
  let π := QuotientGroup.mk' (pCore 2 L)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hk : π.ker = pCore 2 L := by
    ext x
    change QuotientGroup.mk' (pCore 2 L) x = 1 ↔ x ∈ pCore 2 L
    exact QuotientGroup.eq_one_iff x
  have hAQ : ¬ A.subgroupOf L ≤ pCore 2 L := by
    intro hh
    apply reduced_reciprocal_escape h hob models hc hab hd (by change 1 < b F; omega) hcomm hne
    rw [←localGroup_core_eq F d beta]
    intro x hx
    exact ⟨⟨x,hAL hx⟩,hh hx,rfl⟩
  have hπA : (A.subgroupOf L).map π ≠ ⊥ :=
    fun he => hAQ (hk ▸ (Subgroup.map_eq_bot_iff _).mp he)
  obtain ⟨hnW,hN,α,hα,hr,_⟩ := reduced_radius_three_residual_section.{_,0}
    h hob models hc hab hd hb hcomm hne
  let _ := hN
  let X := W ⧸ V₀.subgroupOf W
  let : Finite X := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  let : IsElementaryAbelian 2 A := CommutingThreeProfile.V_elementary F ht.generate
    (fun v => (source_Z_Q_U ht v).1) d.kernel_sylow (by omega) a'
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  have hlo := Representation.SU3.twoGroup_fixedIndex_lower_of_residual_moves H hn hK hconj e
    π hπ (by rw [hk]; exact pCore_isPGroup) (hpW.to_quotient _) α hr
    (A.subgroupOf L) hπA
  exact hlo.trans (quotient_conjugation_fixedIndex_le L W V₀ D A hnW α hα le_sup_right hD)

/-- The terminal unitary marking contradicts the strict denominator index.
The marked quotient is transported to beta by an actual graph conjugator. -/
theorem reduced_radius_three_unitary_contradiction
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
    {K : Type*} [Field K] [Finite K] (H : HermitianForm 3 K)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, H.conj x = x^(2^n))
    (e : Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≃* H.specialSubgroup) ∨
      Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≃*
        ProjectiveSpecialUnitaryMatrixGroup H)) : False := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let : ∀ i, Finite (F i) := finite_endpoints ht
  change 3 < b F at hb
  have hb1 : 1 < b F := by omega
  have hne : ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ ≠ ⊥ := by
    intro hz
    exact hm (bot_unique ((commutator_mono le_rfl (Z_neighbor_le_V F w.property)).trans hz.le))
  have heven : Even ((graph F).dist beta a') := by
    obtain ⟨r,hr⟩ := (source_critical_geometry ht d hc hab hd hb1 hcomm).1
    change b F = 2*r+1 at hr
    change (graph F).dist beta a' + 1 = b F at hd
    refine ⟨r,?_⟩
    have he : (graph F).dist beta a' = 2*r := Nat.add_right_cancel (hd.trans hr)
    simpa only [two_mul] using he
  obtain ⟨g,hg⟩ := (same_orbit_iff F beta a').mpr ((even_dist_iff F ht.generate beta a').mp heven)
  have heq : (d.localGroup beta).map (MulAut.conj g).toMonoidHom = d.localGroup a' := by
    rw [←d.conjugate,hg]
  let f := ((d.localGroup beta).equivMapOfInjective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr heq)
  let ef := QuotientGroup.congr _ _ f (pCore_map_iso 2 f)
  have eβ : Nonempty ((d.localGroup beta ⧸ pCore 2 (d.localGroup beta)) ≃* H.specialSubgroup) ∨
      Nonempty ((d.localGroup beta ⧸ pCore 2 (d.localGroup beta)) ≃*
        ProjectiveSpecialUnitaryMatrixGroup H) := by
    rcases e with he | he
    · exact Or.inl ⟨ef.trans he.some⟩
    · exact Or.inr ⟨ef.trans he.some⟩
  have hl := reduced_radius_three_unitary_fixed_index h hob models hc hab hd hb hcomm
    w hm R hR hcase H hn hK hconj eβ
  obtain ⟨prev,T,_,_,_,_,_,_,_,hu⟩ := reduced_radius_three_section_index h hob models
    hc hab hd hb hcomm hne
  let L := d.localGroup a'
  let : Finite L := Finite.of_injective (inclusion (d.local_le a')) (inclusion_injective _)
  change Sylow 2 L at T
  change Nonempty ((L ⧸ pCore 2 L) ≃* H.specialSubgroup) ∨
    Nonempty ((L ⧸ pCore 2 L) ≃* ProjectiveSpecialUnitaryMatrixGroup H) at e
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup H) :=
    Finite.of_surjective H.specialToProjective H.specialToProjective_surjective
  have hrank : primeRank 2 (L ⧸ pCore 2 L) ≤ n := by
    rcases e with he | he
    · rw [primeRank_congr 2 he.some,primeRank_eq_of_surjective_of_coprime 2 H.specialToProjective
        H.specialToProjective_surjective H.odd_card_specialToProjective_ker.coprime_two_left]
      exact (HermitianForm.EvenTwoRank.two_rank H (by omega) hK hconj).le
    · rw [primeRank_congr 2 he.some]
      exact (HermitianForm.EvenTwoRank.two_rank H (by omega) hK hconj).le
  have hO := (primeRank_le_iff_elementary_card_le (L ⧸ pCore 2 L)).mp hrank
    (omegaCenterIn ((T : Subgroup L).map (QuotientGroup.mk' (pCore 2 L)))) inferInstance
  exact (not_lt_of_ge hl) (hu.trans_le hO)

/-- Every actual terminal model gives the residual contradiction in each
established intersection branch. -/
theorem reduced_radius_three_catalogue_contradiction
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
    : False := by
  cases models a' with
  | linear n hn hi =>
    exact reduced_radius_three_selected_contradiction h hob models hc hab hd hb hcomm
      w hm R hR hcase (Or.inl ⟨n,hn,hi⟩)
  | dihedral hi =>
    exact reduced_radius_three_selected_contradiction h hob models hc hab hd hb hcomm
      w hm R hR hcase (Or.inr (Or.inl hi))
  | suzuki m hi =>
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact reduced_radius_three_selected_contradiction h hob models hc hab hd hb hcomm
        w hm R hR hcase (Or.inr (Or.inr (Or.inl hi)))
    · exact reduced_radius_three_suzuki_contradiction h hob models hc hab hd hb hcomm
        w hm R hR hcase hpos hi.some
  | projective_unitary n hn hi =>
    by_cases hn2 : 2 ≤ n
    · obtain ⟨K,_,_,H,hK,hconj,he⟩ := hi
      exact reduced_radius_three_unitary_contradiction h hob models hc hab hd hb hcomm
        w hm R hR hcase H hn2 hK hconj (Or.inr he)
    · have hn1 : n=1 := by omega
      exact reduced_radius_three_selected_contradiction h hob models hc hab hd hb hcomm
        w hm R hR hcase (Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [hn1,pow_one] using hi)))))
  | special_unitary n hn hi =>
    by_cases hn2 : 2 ≤ n
    · obtain ⟨K,_,_,H,hK,hconj,he⟩ := hi
      exact reduced_radius_three_unitary_contradiction h hob models hc hab hd hb hcomm
        w hm R hR hcase H hn2 hK hconj (Or.inl he)
    · have hn1 : n=1 := by omega
      exact reduced_radius_three_selected_contradiction h hob models hc hab hd hb hcomm
        w hm R hR hcase (Or.inr (Or.inr (Or.inr (Or.inr (by simpa only [hn1,pow_one] using hi)))))

/-- Source parity and the full terminal catalogue leave exactly b=3 or b=5. -/
theorem reduced_distance_le_five
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
    :
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
    exact reduced_radius_three_catalogue_contradiction h hob models hc hab hd (by change 3 < b F; omega) hcomm
      w hm R hR (Or.inl hb7)
  obtain ⟨k,hk⟩ := hodd
  change b F = 2*k+1 at hk
  change b F = 3 ∨ b F = 5
  omega

/-- A linear or dihedral starting quotient gives distance three, with every
terminal model and the moving-neighbor/Sylow premises discharged. -/
theorem reduced_linear_start_distance_three
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
    (hstart : (∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL
      (graphLocalGroup (Reduction.reducedFamily J S₀) a ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a)) 2 (2^n)) ∨
      Nonempty ((graphLocalGroup (Reduction.reducedFamily J S₀) a ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a)) ≃* DihedralGroup 5)) : b (Reduction.reducedFamily J S₀) = 3 := by
  have hb3 := (source_critical_geometry (Reduction.reduced_triple h)
    (Reduction.reducedEarlierLocalTheorems h hob) hc hab hd hb hcomm).2.1
  change 3 ≤ b (Reduction.reducedFamily J S₀) at hb3
  by_contra he
  have hb' : 3 < b (Reduction.reducedFamily J S₀) := by omega
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
  exact reduced_radius_three_catalogue_contradiction h hob models hc hab hd hb' hcomm
    w hm R hR (Or.inr hshape)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
