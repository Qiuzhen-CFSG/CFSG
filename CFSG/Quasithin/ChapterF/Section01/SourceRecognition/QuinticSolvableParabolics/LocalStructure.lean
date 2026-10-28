module

public import CFSG.Quasithin.ChapterF.Section01.SourceLocalResidual
public import Theory.GroupTheory.SylowSmallIndexModels
public import Theory.SpecificGroups.SU3.BinarySylowOrder
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.SpecificGroups.Suzuki.SubgroupParameters
public import Theory.SpecificGroups.DihedralSolvable
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models
public import BenderSuzuki.MatrixGroups.SuzukiZero
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# The actual quintic endpoint before DGS classification

Assume genuine F.1.1, S ≤ K, and [K:S] = 5. The proper local Sylow
normalizer must equal S. Thus the whole Borel is S N_R(S ∩ R), its index
in the first parabolic is five, and the second parabolic is R S. The
first starred parabolic is exactly K, with the same embedded two-core.
Normality of S in the whole Borel is the hypothesis of F.1.10(2)(b).

The faithful five-point quotient action leaves both D₁₀ and Sz(2).
Their orders ten and twenty exclude all binary PSL₂ and unitary-three
quotients: the linear orders are six or at least sixty, and every unitary
three-group has order divisible by eight. The same divisibility excludes
every positive Suzuki parameter. These are filters on actual quotient
isomorphisms, applicable before any marked amalgam is known. The small Ree
type clauses give solvability directly from the full parabolic two-core
quotient, for either orientation, without identifying the amalgam.

Source: Aschbacher–Smith F.1.1–3, F.1.9–12, printed pp.259–264;
Delgado–Goldschmidt–Stellmacher, *Groups and Graphs*, Part II, pp.94–100,
6.1, and 12.9–13.1. DGS's small Ree type conditions concern full parabolic
quotients. Exhaustive DGS alternatives and unconditional opposite solvability
are not asserted here; their assembly remains necessary for the quintic theorem.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] {K R S : Subgroup G}

/-- Prime Sylow index and the proper rank-one normalizer force the local Borel to be S. -/
theorem HypothesisF11.quintic_left_borel (h : HypothesisF11 ![K,R] S)
    (hSK : S ≤ K) (hi : S.relIndex K = 5) : borel K S = S := by
  have hSB : S ≤ borel K S := by
    simpa only [inf_eq_left.mpr hSK] using localSylow_le_borel K S
  have hproper : borel K S < K := (h.rankOneBorelFacts 0).proper
  have hm := relIndex_mul_relIndex S (borel K S) K hSB hproper.le
  rw [hi] at hm
  have hdiv : (borel K S).relIndex K ∣ 5 :=
    ⟨S.relIndex (borel K S), by rw [Nat.mul_comm]; exact hm.symm⟩
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hdiv with h1 | h5
  · exact (hproper.not_ge (relIndex_eq_one.mp h1)).elim
  · rw [h5] at hm
    exact le_antisymm (relIndex_eq_one.mp (by omega)) hSB

/-- Both concrete quintic quotients occur in the input reduction. -/
theorem HypothesisF11.quintic_quotient_cases (h : HypothesisF11 ![K,R] S)
    (hSK : S ≤ K) (hi : S.relIndex K = 5) :
    Nonempty ((K ⧸ pCore 2 K) ≃* DihedralGroup 5) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup 0) := by
  let : Finite K := h.finite_local 0
  obtain ⟨T,hT⟩ := (show ∃ T : Sylow 2 K,
    (T : Subgroup K).map K.subtype = S ⊓ K from h.sylow 0)
  have hT' : (T : Subgroup K) = S.subgroupOf K := by
    apply map_injective K.subtype_injective
    simpa only [Matrix.cons_val_zero, inf_eq_left.mpr hSK,
      map_subgroupOf_eq_of_le hSK] using hT
  have hindex : T.index = 5 := by rw [hT']; exact hi
  have hproper : pCore 2 K < (T : Subgroup K) := by
    refine lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal T) ?_
    intro he
    have hn : (normalizer (T : Set K)) = ⊤ := by
      change normalizer ((T : Subgroup K) : Set K) = ⊤
      rw [←he]
      exact normalizer_eq_top (pCore 2 K)
    exact (rankOneSylowFacts_of_rankOneQuotient
      (show IsRankOneModel (K ⧸ pCore 2 K) from h.quotient 0) T).proper.ne hn
  exact sylow_index_five_core_quotient T hindex hproper

/-- The order alternatives belong to the intrinsic quotient of the original K. -/
theorem HypothesisF11.quintic_quotient_card (h : HypothesisF11 ![K,R] S)
    (hSK : S ≤ K) (hi : S.relIndex K = 5) :
    Nat.card (K ⧸ pCore 2 K) = 10 ∨ Nat.card (K ⧸ pCore 2 K) = 20 := by
  rcases h.quintic_quotient_cases hSK hi with he | he
  · left
    rw [Nat.card_congr he.some.toEquiv,DihedralGroup.nat_card]
  · right
    exact (Nat.card_congr he.some.toEquiv).trans suzukiZero_card

/-- The first full parabolic is solvable, retaining the whole odd Borel. -/
theorem HypothesisF11.quintic_first_solvable (h : HypothesisF11 ![K,R] S)
    (hSK : S ≤ K) (hi : S.relIndex K = 5) :
    Group.IsSolvable (parabolic ![K,R] S 0) := by
  apply (h.parabolic_solvable_iff_local_quotient 0).mpr
  rcases h.quintic_quotient_cases hSK hi with he | he
  · let := GLS3.Chapter5.dihedralGroup_isSolvable 5
    exact Group.isSolvable_of_isSolvable_injective (f := he.some.toMonoidHom) he.some.injective
  · let := suzukiZero_isSolvable
    exact Group.isSolvable_of_isSolvable_injective (f := he.some.toMonoidHom) he.some.injective

/-- The opposite local Borel remains in the whole overlap. -/
theorem HypothesisF11.quintic_commonBorel (h : HypothesisF11 ![K,R] S)
    (hSK : S ≤ K) (hi : S.relIndex K = 5) :
    commonBorel ![K,R] S = S ⊔ borel R S := by
  change (borel K S ⊔ borel R S) ⊔ S = _
  rw [h.quintic_left_borel hSK hi, sup_right_comm, sup_idem]

/-- Adjoining the left local Borel adds nothing to the literal right join. -/
theorem HypothesisF11.quintic_right_parabolic (h : HypothesisF11 ![K,R] S)
    (hSK : S ≤ K) (hi : S.relIndex K = 5) :
    parabolic ![K,R] S 1 = R ⊔ S := by
  change (R ⊔ S) ⊔ borel K S = _
  rw [h.quintic_left_borel hSK hi, sup_assoc, sup_idem]

/-- The full overlap has index five in the first parabolic. -/
theorem HypothesisF11.quintic_borel_index (h : HypothesisF11 ![K,R] S)
    (hSK : S ≤ K) (hi : S.relIndex K = 5) :
    (commonBorel ![K,R] S).relIndex (parabolic ![K,R] S 0) = 5 := by
  let := h.finite_commonBorel
  rw [parabolic_eq_sup_commonBorel,
    relIndex_sup_of_normalizes _ _ (h.commonBorel_normalizes_local 0),
    ←inf_relIndex_right]
  rw [inf_comm, h.local_inf_commonBorel 0]
  change (borel K S).relIndex K = 5
  rw [h.quintic_left_borel hSK hi]
  exact hi

/-- The DGS starred left endpoint equals the original K when S lies in K. -/
theorem HypothesisF11.quintic_starred_left (h : HypothesisF11 ![K,R] S)
    (hSK : S ≤ K) : starredParabolic ![K,R] S 0 = K := by
  exact sup_eq_right.mpr ((h.parabolic_core_le_S 0).trans hSK)

/-- The equality compares the two cores embedded in the same ambient group. -/
theorem HypothesisF11.quintic_left_core (h : HypothesisF11 ![K,R] S)
    (hSK : S ≤ K) : twoCore (parabolic ![K,R] S 0) = twoCore K := by
  simpa only [h.quintic_starred_left hSK] using (h.starredParabolic_same_core 0).symm

/-- F.1.10(2)(b) normality, with no generated-group Sylow assumption. -/
theorem HypothesisF11.quintic_normal_borel (h : HypothesisF11 ![K,R] S)
    (hSK : S ≤ K) : (S.subgroupOf (commonBorel ![K,R] S)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  simpa only [Matrix.cons_val_zero, inf_eq_left.mpr hSK] using
    h.commonBorel_normalizes_localSylow 0

private theorem no_linear_of_card_ten_or_twenty
    {X : Type*} [Group X] (hc : Nat.card X = 10 ∨ Nat.card X = 20)
    {n : ℕ} (hn : 0 < n) : ¬ ClassicalGroup.IsPSL X 2 (2 ^ n) := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have ho := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
  rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (CharTwo.neg_eq 1), mul_one, hF, ← Nat.card_congr e.toEquiv] at ho
  by_cases hn1 : n = 1
  · norm_num [hn1] at ho
    omega
  · have hp : 4 ≤ 2 ^ n := by
      calc
        4 = 2 ^ 2 := rfl
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    have hs : 15 ≤ (2 ^ n) ^ 2 - 1 := by
      have hh : 16 ≤ (2 ^ n) ^ 2 := by nlinarith
      omega
    rcases hc with hc | hc <;> rw [hc] at ho <;> nlinarith

private theorem no_projective_unitary_of_card_ten_or_twenty
    {X : Type*} [Group X] (hc : Nat.card X = 10 ∨ Nat.card X = 20)
    {n : ℕ} (hn : 0 < n) : ¬ ClassicalGroup.IsPSU X 3 (2 ^ n) := by
  rintro ⟨F,_,_,J,hF,hj,⟨e⟩⟩
  have hd := HermitianForm.BinarySylowOrder.cube_dvd_card_projective J
    (by omega : n ≠ 0) hF hj
  rw [←Nat.card_congr e.toEquiv] at hd
  have he : 8 ∣ Nat.card X := (show 8 ∣ (2 ^ n) ^ 3 from by
    change 2 ^ 3 ∣ (2 ^ n) ^ 3
    rw [←pow_mul]
    exact pow_dvd_pow 2 (by omega)).trans hd
  rcases hc with hc | hc <;> norm_num [hc] at he

private theorem no_special_unitary_of_card_ten_or_twenty
    {X : Type*} [Group X] (hc : Nat.card X = 10 ∨ Nat.card X = 20)
    {n : ℕ} (hn : 0 < n) : ¬ IsSU X 3 (2 ^ n) := by
  rintro ⟨F,_,_,J,hF,hj,⟨e⟩⟩
  have hd := (HermitianForm.BinarySylowOrder.cube_dvd_card_projective J
    (by omega : n ≠ 0) hF hj).trans
    (card_dvd_of_surjective J.specialToProjective J.specialToProjective_surjective)
  rw [←Nat.card_congr e.toEquiv] at hd
  have he : 8 ∣ Nat.card X := (show 8 ∣ (2 ^ n) ^ 3 from by
    change 2 ^ 3 ∣ (2 ^ n) ^ 3
    rw [←pow_mul]
    exact pow_dvd_pow 2 (by omega)).trans hd
  rcases hc with hc | hc <;> norm_num [hc] at he

/-- The quintic quotient cannot occupy any binary linear or unitary-three row. -/
theorem HypothesisF11.quintic_excludes_linear_unitary (h : HypothesisF11 ![K,R] S)
    (hSK : S ≤ K) (hi : S.relIndex K = 5) {n : ℕ} (hn : 0 < n) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n) ∧
    ¬ ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 (2 ^ n) ∧
    ¬ IsSU (K ⧸ pCore 2 K) 3 (2 ^ n) :=
  ⟨no_linear_of_card_ten_or_twenty (h.quintic_quotient_card hSK hi) hn,
    no_projective_unitary_of_card_ten_or_twenty (h.quintic_quotient_card hSK hi) hn,
    no_special_unitary_of_card_ten_or_twenty (h.quintic_quotient_card hSK hi) hn⟩

/-- An actual Suzuki marking on the quintic quotient has field order two. -/
theorem HypothesisF11.quintic_suzuki_parameter (h : HypothesisF11 ![K,R] S)
    (hSK : S ≤ K) (hi : S.relIndex K = 5) {m : ℕ}
    (e : (K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup m) : m = 0 := by
  by_contra hm
  have hd : 8 ∣ Nat.card (K ⧸ pCore 2 K) := by
    rw [Nat.card_congr e.toEquiv,suzukiMatrixGroup_card m (by omega)]
    apply dvd_mul_of_dvd_left
    apply dvd_mul_of_dvd_right
    change 2 ^ 3 ∣ (2 ^ (2 * m + 1)) ^ 2
    rw [←pow_mul]
    exact pow_dvd_pow 2 (by omega)
  rcases h.quintic_quotient_card hSK hi with hc | hc <;> norm_num [hc] at hd

variable {L : Fin 2 → Subgroup G}

/-- Either quotient in the small Ree type clauses makes the full parabolic
solvable. This uses precisely the full quotient, with no amalgam recognition. -/
theorem HypothesisF11.parabolic_solvable_of_small_ree_quotient
    (h : HypothesisF11 L S) (i : Fin 2)
    (hq : ClassicalGroup.IsPSL
      (parabolic L S i ⧸ pCore 2 (parabolic L S i)) 2 2 ∨
      Nonempty ((parabolic L S i ⧸ pCore 2 (parabolic L S i)) ≃*
        SuzukiMatrixGroup 0)) :
    Group.IsSolvable (parabolic L S i) := by
  let := h.finite_parabolic i
  have hsol : Group.IsSolvable (parabolic L S i ⧸ pCore 2 (parabolic L S i)) := by
    rcases hq with hlin | hsz
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hlin
      let := Theory.PSL2.OuterSolvable.isSolvable_of_card_two hF
      exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    · let := suzukiZero_isSolvable
      exact Group.isSolvable_of_isSolvable_injective
        (f := hsz.some.toMonoidHom) hsz.some.injective
  let : Group.IsNilpotent (pCore 2 (parabolic L S i)) := pCore_isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 (parabolic L S i))).mpr
    ⟨inferInstance,hsol⟩

end CFSG.Quasithin.ChapterF.Source
