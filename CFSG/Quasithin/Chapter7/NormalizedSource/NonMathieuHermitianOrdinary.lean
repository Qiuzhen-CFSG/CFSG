module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianConstrained
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianParabolics
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourceA5Normality
public import Theory.SpecificGroups.Held.SylowOrderBound
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound

/-!
# Excluding ordinary components in the original Hermitian pushing-up configuration

The literal inclusion of the original residual in the ordinary component,
followed by its central quotient, has solvable kernel. The square-field PSL₃
quotient therefore contributes its full order and an odd-prime rank-two
subgroup to the same component. Binary rank-one and odd-characteristic rows
are already excluded by the original moved module. The rank-two local
normalizer bounds remove the large linear, symplectic, G₂ and triality rows;
fifteen-free two-normalizers remove Ree. Certified orders exclude all finite
rows, including Rudvalis and J₄. Together with the constrained exclusion this
closes the C.2.8 configuration for n > 1.

The Chapter 12 HermitianStrongBounds consumer applies the result to the exact
residual, quotient and moved module produced on the original chosen orbit.
The weak-closure and torus exclusions and the field-four endgame remain open.
Source: Aschbacher--Smith C.3.1--5, printed pp.149--151, applied in 4.4.3 and
7.4.1, pp.619--623 and699--700 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
open CFSG.Quasithin.ChapterA.Section02 CFSG.Quasithin.ClassificationModels
namespace CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian

variable {G E : Type*} [Group G] [Finite G] [Field E] [Finite E]
variable {H M B R W : Subgroup G}

private theorem ordinary_hermitian_map
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (K : Subgroup H) (hK : IsComponent H K) :
    ∃ f : B →* K ⧸ center K, Group.IsSolvable f.ker := by
  have hBH := h.component_le.trans h.local_le
  let a : B ≃* B.subgroupOf H := (subgroupOfEquivOfLe hBH).symm
  let j := (inclusion (h.ordinary_component_contains_original K hK)).comp a.toMonoidHom
  let f := (QuotientGroup.mk' (center K)).comp j
  have hk : f.ker ≤ center B := by
    intro b hb
    have hz : j b ∈ center K := (QuotientGroup.eq_one_iff _).mp hb
    apply mem_center_iff.mpr
    intro c
    apply (inclusion_injective (h.ordinary_component_contains_original K hK)).comp a.injective
    change j (c * b) = j (b * c)
    simpa only [map_mul] using mem_center_iff.mp hz (j c)
  let : CommGroup (center B) := IsMulCommutative.instCommGroup
  exact ⟨f,Group.isSolvable_of_isSolvable_injective (inclusion_injective hk)⟩

omit [Finite E] in
/-- The actual central-quotient inclusion preserves the order of the simple section. -/
theorem ordinary_hermitian_quotient_card_dvd
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    [IsQuasisimple (B ⧸ pCore 2 B)]
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E))
    (K : Subgroup H) (hK : IsComponent H K) :
    Nat.card PSL(3,E) ∣ Nat.card (K ⧸ center K) := by
  let S := (B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)
  let : IsSimpleGroup S := IsQuasisimple.simple
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let π : B →* S := (QuotientGroup.mk' (center (B ⧸ pCore 2 B))).comp
    (QuotientGroup.mk' (pCore 2 B))
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  obtain ⟨f,hf⟩ := ordinary_hermitian_map h K hK
  let := hf
  rw [← Nat.card_congr e.toEquiv]
  exact SimpleSection.card_dvd_of_solvable_representation
    (Group.IsPerfect.not_isSolvable S) π hπ f

private theorem ordinary_hermitian_two_part
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    [IsQuasisimple (B ⧸ pCore 2 B)] {n : ℕ} (hc : Nat.card E = 2^(2*n))
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E))
    (K : Subgroup H) (hK : IsComponent H K) :
    2^(6*n) ∣ Nat.card (K ⧸ center K) := by
  have hd := (Matrix.PSL3.LinearThree.unipotent E).card_subgroup_dvd_card.trans
    (ordinary_hermitian_quotient_card_dvd h e K hK)
  rwa [Matrix.PSL3.LinearThree.card_unipotent,hc,←pow_mul,
    show 2*n*3 = 6*n by omega] at hd

private theorem finite_order_exclusion {N n : ℕ} (hn : 1 < n)
    (hc : Nat.card E = 2^(2*n)) (hd : Nat.card PSL(3,E) ∣ N)
    (h24 : ¬2^24 ∣ N)
    (h16 : ¬(16^3*(16^3-1)*(16^2-1)/Nat.gcd 3 (16-1) : ℕ) ∣ N)
    (h64 : ¬(64^3*(64^3-1)*(64^2-1)/Nat.gcd 3 (64-1) : ℕ) ∣ N) : False := by
  have hu := (Matrix.PSL3.LinearThree.unipotent E).card_subgroup_dvd_card.trans hd
  rw [Matrix.PSL3.LinearThree.card_unipotent,hc,←pow_mul,
    show 2*n*3 = 6*n by omega] at hu
  have hn4 : n < 4 := by
    by_contra! hn4
    exact h24 ((pow_dvd_pow 2 (by omega : 24 ≤ 6*n)).trans hu)
  have hn23 : n = 2 ∨ n = 3 := by omega
  rcases hn23 with rfl | rfl
  · apply h16
    norm_num [Matrix.PSL3.LinearThree.card_projective,hc] at hd ⊢
    exact hd
  · apply h64
    norm_num [Matrix.PSL3.LinearThree.card_projective,hc] at hd ⊢
    exact hd

/-- A split-torus prime gives rank two in the original source span. -/
theorem hermitian_span_odd_rank
    (_h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    [IsQuasisimple (B ⧸ pCore 2 B)] {n : ℕ} (hn : 1 < n)
    (hc : Nat.card E = 2^(2*n))
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ 2 ≤ primeRank p (conjugateSpanBy B M) := by
  obtain ⟨p,hp,hp3,hd⟩ := Nat.BinarySignedTorus.exists_prime_gt_three_dvd_sub
    (by omega : 3 < 2*n)
  let : Fact p.Prime := ⟨hp⟩
  have ho := hp.odd_of_ne_two (by omega : p ≠ 2)
  have hr := Matrix.PSL3.SplitPrimeRank.projective_rank E (by omega : p ≠ 3)
    (by simpa only [hc] using hd)
  have hB : 2 ≤ primeRank p B := by
    by_contra! hB
    let P : Sylow p B := Classical.choice inferInstance
    let f := e.toMonoidHom.comp ((QuotientGroup.mk' (center (B ⧸ pCore 2 B))).comp
      (QuotientGroup.mk' (pCore 2 B)))
    have hf : Function.Surjective f := e.surjective.comp
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
    have hu := P.primeRank_le_one_of_surjective
      (P.isCyclic_of_odd_of_primeRank_le_one ho (by omega)) f hf
    omega
  exact ⟨p,hp,ho,hB.trans (Theory.GroupTheory.primeRank_le_of_injective p
    (inclusion (le_conjugateSpanBy B M)) (inclusion_injective _))⟩

private theorem square_five_dvd_card {n : ℕ} (hc : Nat.card E = 2^(2*n)) :
    5 ∣ Nat.card PSL(3,E) := by
  have hm : Nat.card E ^ 2 % 5 = 1 := by
    rw [hc,←pow_mul,show 2*n*2 = 4*n by omega,pow_mul]
    norm_num [Nat.pow_mod]
  have hp : 1 ≤ Nat.card E ^ 2 := Nat.one_le_pow _ _
    (Nat.le_of_lt (Finite.one_lt_card : 1 < Nat.card E))
  have hd : 5 ∣ Nat.card E ^ 2 - 1 := by omega
  have hd' : 5 ∣ Nat.card PSL(3,E) * Nat.gcd 3 (Nat.card E - 1) := by
    rw [Matrix.PSL3.LinearThree.card_projective_mul_scalar]
    exact dvd_mul_of_dvd_right hd _
  have hcop : Nat.Coprime 5 (Nat.gcd 3 (Nat.card E - 1)) :=
    (by decide : Nat.Coprime 5 3).of_dvd_right (Nat.gcd_dvd_left _ _)
  exact hcop.dvd_of_dvd_mul_right hd'

private theorem no_hermitian_fifteen_free_local
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    [IsQuasisimple (B ⧸ pCore 2 B)] {n : ℕ} (hc : Nat.card E = 2^(2*n))
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E))
    (K : Subgroup H) (hK : IsComponent H K)
    {S : Type*} [Group S] [Finite S] (a : K ⧸ center K ≃* S)
    (hfree : ∀ P : Subgroup S, P ≠ ⊥ → IsPGroup 2 P →
      ¬15 ∣ Nat.card (normalizer (P : Set S))) : False := by
  obtain ⟨_,hP,hne,hn,hr⟩ := h.ordinary_quotient_local_data K hK
  let A := (((conjugateSpanBy B M).subgroupOf H).subgroupOf K).map
    (QuotientGroup.mk' (center K))
  let P := ((R.subgroupOf H).subgroupOf K).map (QuotientGroup.mk' (center K))
  let C := A.map a.toMonoidHom
  let Q := P.map a.toMonoidHom
  have hCN : C ≤ normalizer (Q : Set S) :=
    (map_mono hn).trans (P.le_normalizer_map a.toMonoidHom)
  have hdB : Nat.card PSL(3,E) ∣ Nat.card B := by
    rw [← Nat.card_congr e.toEquiv]
    exact (card_quotient_dvd_card _).trans (card_quotient_dvd_card _)
  have hd (p : ℕ) (hp : p.Prime) (ho : Odd p) (hdp : p ∣ Nat.card PSL(3,E)) :
      p ∣ Nat.card (normalizer (Q : Set S)) := by
    let : Fact p.Prime := ⟨hp⟩
    have hB : 0 < primeRank p B := by
      by_contra! hz
      exact (PrimeRank.eq_zero_iff_not_dvd_card.mp (by omega : primeRank p B = 0))
        (hdp.trans hdB)
    have hspan := hB.trans_le (Theory.GroupTheory.primeRank_le_of_injective p
      (inclusion (le_conjugateSpanBy B M)) (inclusion_injective _))
    have hA : 0 < primeRank p A := by rwa [hr p hp ho]
    have hC : 0 < primeRank p C :=
      lt_of_lt_of_eq hA (primeRank_congr p (a.subgroupMap A))
    have hN := hC.trans_le (Theory.GroupTheory.primeRank_le_of_injective p (inclusion hCN) (inclusion_injective _))
    by_contra hnot
    exact (Nat.ne_of_gt hN) (PrimeRank.eq_zero_iff_not_dvd_card.mpr hnot)
  exact hfree Q (fun he => hne ((map_eq_bot_iff_of_injective P a.injective).mp he))
    (hP.map _) ((show Nat.Coprime 3 5 by decide).mul_dvd_of_dvd_of_dvd
      (hd 3 (by decide) (by decide)
        (Matrix.PSL3.LinearThree.square_three_dvd_card (MulEquiv.refl _) hc))
      (hd 5 (by decide) (by decide) (square_five_dvd_card hc)))

/-- Every literal rank-two Theorem C central quotient is excluded. -/
theorem no_ordinary_hermitian_rankTwo
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    [IsQuasisimple (B ⧸ pCore 2 B)] {n : ℕ} (hn : 1 < n)
    (hc : Nat.card E = 2^(2*n))
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E))
    (K : Subgroup H) (hK : IsComponent H K) {f : ℕ}
    (hm : IsTheoremCRankTwoModel (K ⧸ center K) f) : False := by
  obtain ⟨p,hp,ho,hr⟩ := hermitian_span_odd_rank h hn hc e
  let : Fact p.Prime := ⟨hp⟩
  have hd12 : 2^12 ∣ Nat.card (K ⧸ center K) :=
    (pow_dvd_pow 2 (by omega : 12 ≤ 6*n)).trans (ordinary_hermitian_two_part h hc e K hK)
  cases hm with
  | linear hf hm =>
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
    by_cases hf1 : f = 1
    · rw [Nat.card_congr a.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF,hf1] at hd12
      norm_num at hd12
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    have hu : primeRank p (conjugateSpanBy B M) ≤ 1 := by
      apply h.ordinary_span_primeRank_le_of_model_two_normalizers K hK a ho
      intro A P hA hP hne hN
      let := hA
      by_contra! hb
      obtain ⟨g,point,hg⟩ := MainConverse.LinearThreeGeometry.twoLocal_conjugate_le F
        (by omega) hF (normalizer (P : Set _)) ⟨P,hne,hP,rfl⟩
      let j := (MulAut.conj g).toMonoidHom.comp A.subtype
      have hj : j.range ≤ Matrix.PSL3.RootPlaneGeometry.parabolic F point := by
        refine le_trans ?_ hg
        rintro _ ⟨x,rfl⟩
        exact mem_map_of_mem _ (hN x.property)
      apply Matrix.PSL3.LinearThree.PerfectSubgroups.no_perfect_odd_rank_two_in_parabolic F
        ho (by omega) (by
          rw [hF]
          exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega : 2 ≤ f))
        j ((MulAut.conj g).injective.comp A.subtype_injective)
      cases point
      · exact Or.inr hj
      · exact Or.inl hj
    omega
  | symplectic hf hm =>
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    have hu := h.ordinary_span_primeRank_le_one_of_sp4 K hK
      (a.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm) ho
    omega
  | g2 hf hm =>
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      exact lt_of_lt_of_le (by decide : 2 < 2^2)
        (Nat.pow_le_pow_right (by decide) hf)
    have hu := h.ordinary_span_primeRank_le_one_of_g2 K hK a hlarge ho
    omega
  | triality hf hm =>
    have hu := h.ordinary_span_primeRank_le_one_of_isTrialityGroupAt K hK hf hm ho
    omega
  | ree_f4 m hm hf a =>
    exact no_hermitian_fifteen_free_local h hc e K hK a.some
      (fun P hne hp => ReeF4.ConverseParabolics.normalizer_fifteen_free hm P hne hp)
  | symplectic_derived hf a =>
    rw [Nat.card_congr (a.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).toEquiv,
      nat_card_alternatingGroup] at hd12
    norm_num at hd12
  | g2_derived hf a =>
    rw [Nat.card_congr a.some.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd12
    norm_num at hd12
  | tits hf a =>
    rw [Nat.card_congr a.some.toEquiv,Tits.parrottGroup_card] at hd12
    norm_num at hd12

/-- No ordinary component contains the original Hermitian source configuration. -/
theorem no_ordinary_hermitian_component
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    [IsQuasisimple (B ⧸ pCore 2 B)] {n : ℕ} (hn : 1 < n)
    (hc : Nat.card E = 2^(2*n))
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E))
    (K : Subgroup H) (hK : IsComponent H K) : False := by
  let := hK.2
  have hm := Chapter1.QuasisimpleInvolutions.quotient_model (h.sqtk.subgroup K)
    theoremA_knownSimple theoremC_knownSimple
  have hd := ordinary_hermitian_quotient_card_dvd h e K hK
  have hd12 : 2^12 ∣ Nat.card (K ⧸ center K) :=
    (pow_dvd_pow 2 (by omega : 12 ≤ 6*n)).trans (ordinary_hermitian_two_part h hc e K hK)
  cases hm with
  | alternating m hm a =>
    rw [Nat.card_congr a.some.toEquiv] at hd12
    have hdperm := hd12.trans (alternatingGroup (Fin m)).card_subgroup_dvd_card
    rw [Nat.card_perm,Nat.card_fin] at hdperm
    interval_cases m <;> norm_num at hdperm
  | odd hm => exact h.no_ordinary_component_of_theoremC_odd_model K hK hm
  | bender hm =>
    cases hm with
    | linear f hf hm =>
      obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      exact h.no_ordinary_component_sl2_central_quotient K hK
        (a.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm)
    | unitary f hf hm => exact h.no_ordinary_component_binary_unitary_three K hK hf hm
    | suzuki m hm a => exact h.no_ordinary_component_suzuki_central_quotient K hK hm a.some
  | rank_two f hm => exact no_ordinary_hermitian_rankTwo h hn hc e K hK hm
  | linear_binary m hm a =>
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := a
    rw [Nat.card_congr a.toEquiv] at hd12
    rcases hm with rfl | rfl
    · have hcard := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
      norm_num [hF,Fin.prod_univ_succ] at hcard
      rw [hcard] at hd12
      norm_num at hd12
    · have hcard := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
      norm_num [hF,Fin.prod_univ_succ] at hcard
      rw [hcard] at hd12
      norm_num at hd12
  | sporadic hm =>
    rcases hm with ⟨name,hname,⟨a⟩⟩ | ⟨a⟩
    · rw [Nat.card_congr a.toEquiv] at hd hd12
      cases name with
      | m11 =>
        change 2^12 ∣ Nat.card Sporadic.Mathieu.M11 at hd12
        rw [Sporadic.Mathieu.m11_order] at hd12
        norm_num at hd12
      | m12 =>
        change 2^12 ∣ Nat.card Sporadic.Mathieu.M12 at hd12
        rw [Sporadic.Mathieu.m12_order] at hd12
        norm_num at hd12
      | m22 =>
        change 2^12 ∣ Nat.card Sporadic.Mathieu.M22 at hd12
        rw [Sporadic.Mathieu.m22_order] at hd12
        norm_num at hd12
      | m23 =>
        change 2^12 ∣ Nat.card Sporadic.Mathieu.M23 at hd12
        rw [Sporadic.Mathieu.m23_order] at hd12
        norm_num at hd12
      | m24 =>
        change 2^12 ∣ Nat.card Sporadic.Mathieu.M24 at hd12
        rw [Sporadic.Mathieu.m24_order] at hd12
        norm_num at hd12
      | j2 =>
        change 2^12 ∣ Nat.card Sporadic.LeechRelated.J2.Carrier at hd12
        rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hd12
        norm_num at hd12
      | j3 => exact hname rfl
      | hs =>
        have hh := hd12.trans Sporadic.LeechRelated.HS.card_carrier_dvd
        norm_num at hh
      | he => exact Held.not_two_pow_twelve_dvd_card hd12
      | ru =>
        change Nat.card PSL(3,E) ∣ Nat.card Rudvalis.Model at hd
        rw [Rudvalis.model_card] at hd
        exact finite_order_exclusion hn hc hd (by norm_num) (by norm_num) (by norm_num)
      | j4 =>
        change Nat.card PSL(3,E) ∣ Nat.card Janko4.Model at hd
        rw [Janko4.Cardinality.model_card] at hd
        exact finite_order_exclusion hn hc hd (by norm_num) (by norm_num) (by norm_num)
    · exact h.no_ordinary_component_janko_central_quotient K hK a.some

/-- The ordinary and constrained exclusions close the original C.2.8 alternative. -/
theorem no_hermitian_pushingUp
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hstrict : M < H) (hN : (B.subgroupOf M).Normal)
    [IsQuasisimple (B ⧸ pCore 2 B)] {n : ℕ} (hn : 1 < n)
    (hc : Nat.card E = 2^(2*n))
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E)) : False := by
  obtain ⟨K,hK,_⟩ := pushingUp_ordinary_component h hstrict hN hn hc e
  exact no_ordinary_hermitian_component h hn hc e K hK

end CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian
