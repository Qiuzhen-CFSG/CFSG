module

public import Stellmacher.Recognition.MinimalSimpleOddCoreOvergroups
public import Stellmacher.Recognition.OddCoreQuotientControl
public import Stellmacher.Recognition.OddCoreWeakSylow
public import Stellmacher.Recognition.CentricInvolutionFusion
public import Theory.GroupTheory.ElementaryWeakCoreCentralFusion
public import Theory.GroupTheory.SolvableFourNormalizerSupplement
public import Theory.GroupTheory.RankTwoOddQuotient

/-!
# Internal control in the rank-two odd quotient case

Let M be a proper overgroup of the completed odd-core normalizer. Suppose
its odd quotient has two-core of elementary rank at most two and has no
normal elementary four-group. Its two-core contains a four, so the cyclic
center argument supplies a central involution in the quotient. Lift it to
the chosen Sylow subgroup to obtain a Sylow-central involution t.

Ambient simple-group fusion supplies a centric normalizer moving t within
the Sylow subgroup. The N₂ weak-core theorem and the elementary weak-core
central-fusion lemma put that normalizer in M. But the quotient image of t
is central, and the odd quotient map is injective on the Sylow subgroup.
Thus the conjugate equals t, a contradiction. This uses the ambient
minimal-simple hypotheses, not purely solvable component connectivity.

The earlier centralizer supplement and escape interfaces are preserved.
The final theorem proves the requested internal containment; it does not
address normalizers escaping the chosen maximal overgroup.

Sources: GLS2, Chapter F, Sections 21–22; GLS4, Chapter 2, Lemmas 18.7–18.8,
printed p.94. The ambient fusion input uses the centric fusion relation and
the Glauberman Z-star theorem.
-/

namespace Stellmacher.Recognition

/-- In the remaining quotient case, an involution centralizing the ambient
Sylow subgroup has centralizer in M supplementing the odd core of M. -/
public theorem minimalSimple_oddCore_internal_rank_two_centralizer_supplement
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A M : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (S : Sylow 2 G) (hAS : A ≤ S) (hM : M < ⊤)
    (hNM : Subgroup.normalizer (involutionOddCoreClosure A : Set G) ≤ M)
    (hsmall : ∀ D : Subgroup (M ⧸ pPrimeCore 2 M), IsElementaryAbelian 2 D →
      D ≤ pCore 2 (M ⧸ pPrimeCore 2 M) → Nat.card D < 8)
    (hno : ∀ U : Subgroup (M ⧸ pPrimeCore 2 M), U.Normal →
      IsElementaryAbelian 2 U → Nat.card U ≠ 4) :
    ∃ t : G, orderOf t = 2 ∧ t ∈ S ∧
      (S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G) ∧
      M = (pPrimeCore 2 M).map M.subtype ⊔
        (M ⊓ Subgroup.centralizer ({t} : Set G)) := by
  let X := M ⧸ pPrimeCore 2 M
  let : Group.IsSolvable M := hG.solvable_of_lt M hM
  have hSM : (S : Subgroup G) ≤ M :=
    (sylow_le_normalizer_oddCoreClosure hG.isNTwoGroup S A hAS hA).trans hNM
  have hAM := hAS.trans hSM
  let : IsElementaryAbelian 2 (A.subgroupOf M) := IsElementaryAbelian.subgroupOf hAM
  obtain ⟨D, hDQ, hDe, hDcard⟩ :=
    exists_elementary_four_le_pCore_odd_quotient_of_solvable (A.subgroupOf M)
      (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv])
  have hQne : pCore 2 X ≠ ⊥ := by
    intro h
    have hDbot : D = ⊥ := bot_unique (hDQ.trans_eq h)
    have hDone : Nat.card D = 1 := Subgroup.card_eq_one.mpr hDbot
    omega
  obtain ⟨z, hz, hzc, -⟩ := Subgroup.exists_central_involution_of_rank_two_normal_twoGroup
    (pCore 2 X) pCore_isPGroup hQne hsmall hno
  obtain ⟨t, ht, htS, hSC, -, hsupp⟩ :=
    Subgroup.exists_sylow_central_involution_supplement_of_odd_quotient
      (pPrimeCore 2 M) pPrimeCore_coprime_card (S.subtype hSM) z hz hzc
  have hSCG : (S : Subgroup G) ≤ Subgroup.centralizer ({(t : G)} : Set G) := by
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (Subgroup.mem_centralizer_singleton_iff.mp (hSC (show (⟨s, hSM hs⟩ : M) ∈
        S.subtype hSM from hs))))
  refine ⟨t, (Subgroup.orderOf_coe t).trans ht, htS, hSCG, ?_⟩
  apply le_antisymm
  · have htop : (⊤ : Subgroup M) ≤
        ((pPrimeCore 2 M).map M.subtype ⊔
          (M ⊓ Subgroup.centralizer ({(t : G)} : Set G))).subgroupOf M := by
      rw [← hsupp]
      apply sup_le
      · intro x hx
        exact (le_sup_right : M ⊓ Subgroup.centralizer ({(t : G)} : Set G) ≤ _)
          ⟨x.property, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
            (Subgroup.mem_centralizer_singleton_iff.mp hx))⟩
      · intro x hx
        exact (le_sup_left : (pPrimeCore 2 M).map M.subtype ≤ _)
          (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    intro x hx
    exact htop (Subgroup.mem_top (⟨x, hx⟩ : M))
  · exact sup_le (Subgroup.map_subtype_le _) inf_le_left

/-- Failure of internal control is already witnessed inside the centralizer
of a Sylow-central involution, even after intersecting that centralizer with M. -/
public theorem minimalSimple_oddCore_internal_rank_two_centralizer_escape
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A M : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (S : Sylow 2 G) (hAS : A ≤ S) (hM : M < ⊤)
    (hNM : Subgroup.normalizer (involutionOddCoreClosure A : Set G) ≤ M)
    (hsmall : ∀ D : Subgroup (M ⧸ pPrimeCore 2 M), IsElementaryAbelian 2 D →
      D ≤ pCore 2 (M ⧸ pPrimeCore 2 M) → Nat.card D < 8)
    (hno : ∀ U : Subgroup (M ⧸ pPrimeCore 2 M), U.Normal →
      IsElementaryAbelian 2 U → Nat.card U ≠ 4)
    (hnot : ¬ M ≤ Subgroup.normalizer (involutionOddCoreClosure A : Set G)) :
    ∃ t : G, orderOf t = 2 ∧ t ∈ S ∧
      (S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G) ∧
      ¬ M ⊓ Subgroup.centralizer ({t} : Set G) ≤
        Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  obtain ⟨t, ht, htS, hSC, hsupp⟩ :=
    minimalSimple_oddCore_internal_rank_two_centralizer_supplement
      hG A M hA S hAS hM hNM hsmall hno
  refine ⟨t, ht, htS, hSC, ?_⟩
  intro hc
  apply hnot
  rw [hsupp]
  exact sup_le (minimalSimple_oddCore_overgroup_sandwich hG A M hA hM hNM).2 hc

/-- Ambient involution fusion excludes the residual rank-two odd quotient
inside every proper overgroup of the completed odd-core normalizer. -/
public theorem minimalSimple_oddCore_internal_rank_two_exclusion
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A M : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (S : Sylow 2 G) (hAS : A ≤ S) (hM : M < ⊤)
    (hNM : Subgroup.normalizer (involutionOddCoreClosure A : Set G) ≤ M)
    (hsmall : ∀ D : Subgroup (M ⧸ pPrimeCore 2 M), IsElementaryAbelian 2 D →
      D ≤ pCore 2 (M ⧸ pPrimeCore 2 M) → Nat.card D < 8)
    (hno : ∀ U : Subgroup (M ⧸ pPrimeCore 2 M), U.Normal →
      IsElementaryAbelian 2 U → Nat.card U ≠ 4) : False := by
  let _ := hG.isSimpleGroup
  let X := M ⧸ pPrimeCore 2 M
  let : Group.IsSolvable M := hG.solvable_of_lt M hM
  have hSM : (S : Subgroup G) ≤ M :=
    (sylow_le_normalizer_oddCoreClosure hG.isNTwoGroup S A hAS hA).trans hNM
  have hAM := hAS.trans hSM
  let : IsElementaryAbelian 2 (A.subgroupOf M) := IsElementaryAbelian.subgroupOf hAM
  obtain ⟨E, hEQ, hEe, hEcard⟩ :=
    exists_elementary_four_le_pCore_odd_quotient_of_solvable (A.subgroupOf M)
      (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv])
  have hQne : pCore 2 X ≠ ⊥ := by
    intro h
    have hEbot : E = ⊥ := bot_unique (hEQ.trans_eq h)
    have hEone : Nat.card E = 1 := Subgroup.card_eq_one.mpr hEbot
    omega
  obtain ⟨z, hz, hzc, -⟩ := Subgroup.exists_central_involution_of_rank_two_normal_twoGroup
    (pCore 2 X) pCore_isPGroup hQne hsmall hno
  obtain ⟨t, ht, htS, hSC, htz, -⟩ :=
    Subgroup.exists_sylow_central_involution_supplement_of_odd_quotient
      (pPrimeCore 2 M) pPrimeCore_coprime_card (S.subtype hSM) z hz hzc
  have htG : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  have htZ : (t : G) ∈ (Subgroup.center (S : Subgroup G)).map
      (S : Subgroup G).subtype := by
    refine Subgroup.mem_map.mpr ⟨⟨t, htS⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro s
    apply Subtype.ext
    exact congrArg (fun x : M => (x : G)) (Subgroup.mem_centralizer_singleton_iff.mp
      (hSC (show (⟨s, hSM s.property⟩ : M) ∈ S.subtype hSM from s.property)))
  obtain ⟨D, -, hcentric, hDS, -, g, hg, hgtD, hmove⟩ :=
    exists_centric_extremal_normalizer_moves_involution hG.not_isSolvable S
      ⟨t, htS⟩ ((Subgroup.orderOf_coe (⟨(t : G), htS⟩ : S)).symm.trans htG)
  have hND : Subgroup.normalizer (D : Set G) ≤ M := by
    apply Subgroup.normalizer_le_of_moving_central_involution (S : Subgroup G) M A D
      S.isPGroup' hSM hA hAS ?_ (t : G) htG htZ hDS hcentric g⁻¹
      ((Subgroup.normalizer (D : Set G)).inv_mem hg)
      (by simpa only [inv_inv] using hmove)
    intro E B hEe hE4 hES hBe hB8 hBC
    let : IsElementaryAbelian 2 E := hEe
    let : IsElementaryAbelian 2 B := hBe
    exact (normalizer_le_normalizer_oddCoreClosure_of_weak_rank
      hG.not_isSolvable hG.isNTwoGroup S A E E B hAS hA hES le_rfl hE4
      (hBC.trans le_sup_right) hB8).trans hNM
  let gm : M := ⟨g, hND hg⟩
  let q := QuotientGroup.mk' (pPrimeCore 2 M)
  have hinj := Subgroup.injective_comp_subtype_of_coprime_ker q
    (by simpa only [q, QuotientGroup.ker_mk'] using
      (pPrimeCore_coprime_card (p := 2) (G := M)))
    (S.subtype hSM) (S.subtype hSM).isPGroup'
  have hconjS : gm⁻¹ * t * gm ∈ S.subtype hSM := hDS hgtD
  have heq : (⟨gm⁻¹ * t * gm, hconjS⟩ : S.subtype hSM) = ⟨t, htS⟩ := by
    apply hinj
    change q (gm⁻¹ * t * gm) = q t
    rw [map_mul, map_mul, map_inv, htz]
    rw [Subgroup.mem_center_iff.mp hzc ((q gm)⁻¹)]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  apply hmove
  exact congrArg (fun x : S.subtype hSM => ((x : M) : G)) heq

/-- Internal control in the residual rank-two odd quotient case. The additional
quotient hypotheses are impossible by ambient involution fusion. This does not
address a normalizer escaping the chosen maximal overgroup. -/
public theorem minimalSimple_oddCore_internal_rank_two_control
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (_hR : involutionOddCoreClosure A ≠ ⊥) (S : Sylow 2 G) (hAS : A ≤ S)
    (Q : Subgroup G) (_hQ : Q ≠ ⊥) (_hQtwo : IsPGroup 2 Q) (_hQS : Q ≤ S)
    (_hQsmall : ∀ B : Subgroup G, B ≤ Q → IsElementaryAbelian 2 B → Nat.card B < 8)
    (M : Subgroup G) (hM : IsCoatom M)
    (hNM : Subgroup.normalizer (involutionOddCoreClosure A : Set G) ≤ M)
    (_hQM : Subgroup.normalizer (Q : Set G) ≤ M)
    (hsmall : ∀ D : Subgroup (M ⧸ pPrimeCore 2 M), IsElementaryAbelian 2 D →
      D ≤ pCore 2 (M ⧸ pPrimeCore 2 M) → Nat.card D < 8)
    (hno : ∀ U : Subgroup (M ⧸ pPrimeCore 2 M), U.Normal →
      IsElementaryAbelian 2 U → Nat.card U ≠ 4) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) :=
  (minimalSimple_oddCore_internal_rank_two_exclusion hG A M hA S hAS
    (lt_top_iff_ne_top.mpr hM.ne_top) hNM hsmall hno).elim

end Stellmacher.Recognition
