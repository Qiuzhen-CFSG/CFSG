module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.RankTwoDistinctness
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import Theory.SpecificGroups.Classical.EvenDerivedThree

/-!
# Complete containing-pair exclusions in three binary rank-two families

Pass the original local factor through the containing component's actual
two-core quotient. A proper full-Sylow local component of binary PSL₃,
Sp₄ or G₂ is a parabolic residual with intrinsic quotient SL₂ over the
same field. In the full-image case the ambient model itself contains a
cubic. In either case, cubic divisibility lifts to L and survives its
intrinsic two-core quotient.

The final applications combine this calculation with RankTwoDistinctness
and the existing three-divisor contradiction. They exclude either member
of the actual containing pair in each of these families, without an extra
distinctness or cubic-divisibility premise. Both original factors, the
prescribed Sylow, the half-join and the actual exchanger are retained.

The other containing models, the three-free enlargement and the zero-kernel
binary-three normalizer remain with qt-d-10-nona5-half-sylow-unique, which
also retains final assembly. ModuleChoiceAt is supplied independently by
qt-d-10-nona5-point-selection; qt-d-10-nona5-point-control retains its
ultimate discharge. No unconditional half-Sylow theorem is asserted here.
Source: Aschbacher--Smith A.3.12 and 10.2.6, pp.47--48 and748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

private theorem linear_two_three_dvd (F : Type*) [Field F] [Finite F] [CharP F 2] :
    3 ∣ Nat.card SL(2,F) :=
  ((Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
    (F := F) (i := (0 : Fin 2)) (j := 1) (by decide)).trans (card_subgroup_dvd_card _)).trans
      (card_quotient_dvd_card _)

private theorem ContainingPair.three_dvd_of_local_cubic
    (C : ContainingPair D H t K₁ K₂)
    {s : G} (hs : s ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn H)
    (hBK : L.map (MulAut.conj s).toMonoidHom ≤ K)
    {X : Type*} [Group X] [Finite X] (e : (K ⧸ pCore 2 K) ≃* X)
    (hX : 3 ∣ Nat.card X)
    (hloc : ∀ (S : Sylow 2 X) (A : Subgroup X),
      A ∈ localCComponents S → A ≠ ⊤ → 3 ∣ Nat.card A) :
    3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  obtain ⟨S,_,hl⟩ := C.local_sylow_in_containing hs hK hBK
  let B := (L.map (MulAut.conj s).toMonoidHom).subgroupOf K
  let b : L ≃* B := ((MulAut.conj s).subgroupMap L).trans (subgroupOfEquivOfLe hBK).symm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent q.ker := hk.symm ▸ pCore_isNilpotent
  have hA : B.map q ∈ localCComponents (S.mapSurjective hq) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hl q
  have hdA : 3 ∣ Nat.card (B.map q) := by
    by_cases he : B.map q = ⊤
    · rw [he,Nat.card_congr (topEquiv : (⊤ : Subgroup X) ≃* X).toEquiv]
      exact hX
    · exact hloc (S.mapSurjective hq) _ hA he
  have hdB : 3 ∣ Nat.card B := hdA.trans
    (card_dvd_of_surjective (q.subgroupMap B) (q.subgroupMap_surjective B))
  have hdL : 3 ∣ Nat.card L := (Nat.card_congr b.toEquiv).symm ▸ hdB
  by_contra hd
  have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hd
  rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 L) pCore_isPGroup] at hz
  exact PrimeRank.eq_zero_iff_not_dvd_card.mp hz hdL

/-- The literal full-Sylow local factor in a binary PSL₃ quotient contains a cubic.
This also rules out a Suzuki original factor in that containing model. -/
theorem ContainingPair.three_dvd_of_linear_three_quotient
    (C : ContainingPair D H t K₁ K₂)
    {s : G} (hs : s ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn H)
    (hBK : L.map (MulAut.conj s).toMonoidHom ≤ K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K ⧸ pCore 2 K) ≃* PSL(3,F)) : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  apply C.three_dvd_of_local_cubic hs hK hBK e
  · exact (Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
      (F := F) (i := (0 : Fin 3)) (j := 1) (by decide)).trans (card_subgroup_dvd_card _)
  · intro S A hA hne
    obtain ⟨a⟩ := SourceEmbeddings.linear_three_local_core_quotient hF hn S A hA hne
    have h3 : 3 ∣ Nat.card (A ⧸ pCore 2 A) :=
      (Nat.card_congr a.toEquiv).symm ▸ linear_two_three_dvd F
    exact h3.trans (card_quotient_dvd_card _)

/-- The same cubic survives in every original factor contained in binary Sp₄. -/
theorem ContainingPair.three_dvd_of_symplectic_four_quotient
    (C : ContainingPair D H t K₁ K₂)
    {s : G} (hs : s ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn H)
    (hBK : L.map (MulAut.conj s).toMonoidHom ≤ K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K ⧸ pCore 2 K) ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
    3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  apply C.three_dvd_of_local_cubic hs hK hBK e
  · exact Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_sp4_commutator.trans
      (card_subgroup_dvd_card _)
  · intro S A hA hne
    obtain ⟨g,hg⟩ := SourceEmbeddings.FiveLocalFF.symplectic_local_placement hF hn S A hA hne
    let a := (MulAut.conj g).subgroupMap A
    let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
    have he : Nonempty (((A.map (MulAut.conj g).toMonoidHom) ⧸
        pCore 2 (A.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)) := by
      rcases hg with hg | hg
      · rw [hg]
        exact ⟨Theory.SpecificGroups.SymplecticFour.pointLocalCoreQuotientEquiv hF hn⟩
      · rw [hg]
        exact ⟨Theory.SpecificGroups.SymplecticFour.planeLocalCoreQuotientEquiv hF hn⟩
    have h3 : 3 ∣ Nat.card (A ⧸ pCore 2 A) :=
      (Nat.card_congr (aq.trans he.some).toEquiv).symm ▸ linear_two_three_dvd F
    exact h3.trans (card_quotient_dvd_card _)

/-- Both G₂ parabolic residuals have the same literal SL₂ two-core quotient. -/
theorem ContainingPair.three_dvd_of_g2_quotient
    (C : ContainingPair D H t K₁ K₂)
    {s : G} (hs : s ∈ (T : Subgroup G)) {K : Subgroup G}
    (hK : K ∈ cComponentsIn H)
    (hBK : L.map (MulAut.conj s).toMonoidHom ≤ K)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : (K ⧸ pCore 2 K) ≃* Atlas.G2.Model F) : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  apply C.three_dvd_of_local_cubic hs hK hBK e
  · have hr := (Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2 (F := F)).trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator (Atlas.G2.Model F)).subtype Subtype.val_injective)
    by_contra hd
    have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hd
    omega
  · intro S A hA hne
    obtain ⟨g,hg⟩ := SourceEmbeddings.FiveLocalFF.G2.local_placement hF S A hA hne
    let a := (MulAut.conj g).subgroupMap A
    let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
    have he : Nonempty (((A.map (MulAut.conj g).toMonoidHom) ⧸
        pCore 2 (A.map (MulAut.conj g).toMonoidHom)) ≃* SL(2,F)) := by
      rcases hg with hg | hg
      · rw [hg]
        exact ⟨(QuotientGroup.quotientMulEquivOfEq Atlas.G2.LieParabolicSetup.local₁_intrinsic_pCore).trans
          Atlas.G2.LieParabolicSetup.local₁RadicalQuotientEquivSL⟩
      · rw [hg]
        exact ⟨(QuotientGroup.quotientMulEquivOfEq Atlas.G2.LieParabolicSetup.local₂_pCore).trans
          Atlas.G2.LieParabolicSetup.local₂RadicalQuotientEquivSL⟩
    have h3 : 3 ∣ Nat.card (A ⧸ pCore 2 A) :=
      (Nat.card_congr (aq.trans he.some).toEquiv).symm ▸ linear_two_three_dvd F
    exact h3.trans (card_quotient_dvd_card _)

private theorem ContainingPair.first_image_data (C : ContainingPair D H t K₁ K₂) :
    K₁.map H.subtype ∈ cComponentsIn H ∧
    L.map (MulAut.conj (1 : G)).toMonoidHom ≤ K₁.map H.subtype := by
  have hmap : (K₁.map H.subtype).subgroupOf H = K₁ :=
    comap_map_eq_self_of_injective H.subtype_injective K₁
  refine ⟨⟨map_subtype_le _,hmap.symm ▸ C.first_component⟩,?_⟩
  have h := map_mono (f := H.subtype) C.first_le
  rw [map_subgroupOf_eq_of_le C.left_le] at h
  have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  simpa only [hid,Subgroup.map_id] using h

/-- The complete pair exclusion when the first intrinsic quotient is binary
PSL₃: both distinctness and cubic divisibility are proved from the actual model. -/
theorem ContainingPair.impossible_of_first_linear_three_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hnn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K₁ ⧸ pCore 2 K₁) ≃* PSL(3,F)) : False := by
  obtain ⟨hK,hLK⟩ := C.first_image_data
  let a := (K₁.equivMapOfInjective H.subtype H.subtype_injective).symm
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  exact C.impossible_of_three_and_first_linear_three_quotient hchoice hmany hn hna
    (C.three_dvd_of_linear_three_quotient (one_mem _) hK hLK hnn hF b) hnn hF e

/-- The complete pair exclusion for a binary Sp₄ first intrinsic quotient. -/
theorem ContainingPair.impossible_of_first_symplectic_four_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hnn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K₁ ⧸ pCore 2 K₁) ≃* Theory.SpecificGroups.SymplecticFour.Sp F) : False := by
  obtain ⟨hK,hLK⟩ := C.first_image_data
  let a := (K₁.equivMapOfInjective H.subtype H.subtype_injective).symm
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) (by omega))
  exact C.impossible_of_three_and_first_symplectic_four_quotient hchoice hmany hn hna
    (C.three_dvd_of_symplectic_four_quotient (one_mem _) hK hLK hnn hF b) hlarge e

/-- The complete pair exclusion for a binary G₂ first intrinsic quotient. -/
theorem ContainingPair.impossible_of_first_g2_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : (K₁ ⧸ pCore 2 K₁) ≃* Atlas.G2.Model F) : False := by
  obtain ⟨hK,hLK⟩ := C.first_image_data
  let a := (K₁.equivMapOfInjective H.subtype H.subtype_injective).symm
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  exact C.impossible_of_three_and_first_g2_quotient hchoice hmany hn hna
    (C.three_dvd_of_g2_quotient (one_mem _) hK hLK hF b) hF e

private theorem ContainingPair.second_image_data (C : ContainingPair D H t K₁ K₂) :
    K₂.map H.subtype ∈ cComponentsIn H ∧
    L.map (MulAut.conj t).toMonoidHom ≤ K₂.map H.subtype := by
  have hmap : (K₂.map H.subtype).subgroupOf H = K₂ :=
    comap_map_eq_self_of_injective H.subtype_injective K₂
  refine ⟨⟨map_subtype_le _,hmap.symm ▸ C.second_component⟩,?_⟩
  have h := map_mono (f := H.subtype) C.second_le
  rwa [map_subgroupOf_eq_of_le C.right_le] at h

/-- The same PSL₃ exclusion on the second member keeps the original exchanger. -/
theorem ContainingPair.impossible_of_second_linear_three_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hnn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K₂ ⧸ pCore 2 K₂) ≃* PSL(3,F)) : False := by
  have hne : K₁ ≠ K₂ := by
    intro he
    subst K₂
    exact C.distinct_of_first_linear_three_quotient hn hnn hF e rfl
  obtain ⟨hK,hLK⟩ := C.second_image_data
  let a := (K₂.equivMapOfInjective H.subtype H.subtype_injective).symm
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  exact C.impossible_of_distinct_three hchoice hmany hn hna hne
    (C.three_dvd_of_linear_three_quotient C.t_mem hK hLK hnn hF b)

/-- The symplectic exclusion on the second member uses the same half-Sylow. -/
theorem ContainingPair.impossible_of_second_symplectic_four_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hnn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K₂ ⧸ pCore 2 K₂) ≃* Theory.SpecificGroups.SymplecticFour.Sp F) : False := by
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hne : K₁ ≠ K₂ := by
    intro he
    subst K₂
    exact C.distinct_of_first_symplectic_four_quotient hn hlarge e rfl
  obtain ⟨hK,hLK⟩ := C.second_image_data
  let a := (K₂.equivMapOfInjective H.subtype H.subtype_injective).symm
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  exact C.impossible_of_distinct_three hchoice hmany hn hna hne
    (C.three_dvd_of_symplectic_four_quotient C.t_mem hK hLK hnn hF b)

/-- The G₂ exclusion on the second member requires no extra rank premise. -/
theorem ContainingPair.impossible_of_second_g2_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (e : (K₂ ⧸ pCore 2 K₂) ≃* Atlas.G2.Model F) : False := by
  have hne : K₁ ≠ K₂ := by
    intro he
    subst K₂
    exact C.distinct_of_first_g2_quotient hn hF e rfl
  obtain ⟨hK,hLK⟩ := C.second_image_data
  let a := (K₂.equivMapOfInjective H.subtype H.subtype_injective).symm
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  exact C.impossible_of_distinct_three hchoice hmany hn hna hne
    (C.three_dvd_of_g2_quotient C.t_mem hK hLK hF b)

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
