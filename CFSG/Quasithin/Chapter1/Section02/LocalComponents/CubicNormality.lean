module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ThreeResidualOrbit
public import Theory.SpecificGroups.Janko1.Model.Certification
public import Theory.SpecificGroups.Classical.EvenDerivedThree
public import Theory.SpecificGroups.PSL2.PrimeCubicRank

/-!
# A cubic outside a normal subgroup forces component normality

A nonnormal C-component of an SQTK group has one of the four original
models. If its two-core quotient has order divisible by three, the known
component-orbit theorem identifies its normal closure with O^{3′}.
Thus a normal subgroup containing that component must contain every cubic
element. An actual cubic outside the subgroup forces component normality.

The plane-centralizer application is in Chapter13's
`OriginalPlaneCentralizers.Extraction.CubicResidual`; it retains the literal
plane centralizer inside its normalizer.
Source: Aschbacher--Smith 1.2.1--2, pp.504--505, and 13.3.12, p.889.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]

private theorem simple_of_linear {Q : Type*} [Group Q] [Finite Q]
    [IsQuasisimple Q] {q : ℕ} (h : ClassicalGroup.IsPSL Q 2 q) : IsSimpleGroup Q := by
  obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
  have hz : center Q = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh : e x ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      (centerCongr e ⟨x, hx⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot F, mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup

private theorem simple_of_three_dvd_model {Q : Type*} [Group Q] [Finite Q]
    [IsQuasisimple Q] (hm : NonnormalCComponentModel Q) (hd : 3 ∣ Nat.card Q) :
    IsSimpleGroup Q := by
  cases hm with
  | linear_even n hn he => exact simple_of_linear he
  | linear_prime p hp ho he => exact simple_of_linear he
  | suzuki m hm he =>
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv] at hd
    exact (BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega) hd).elim
  | janko he => exact he.some.isSimpleGroup

/-- A cubic outside the given normal subgroup excludes a nonnormal cubic component. -/
theorem component_normal_of_cubic_outside_normal
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (H : Subgroup G) [H.Normal] {J : Subgroup G} (hJ : J.IsCComponent)
    [IsQuasisimple (J ⧸ pCore 2 J)] (hJH : J ≤ H)
    (hd : 3 ∣ Nat.card (J ⧸ pCore 2 J))
    (x : G) (hx : orderOf x = 3) (hout : x ∉ H) : J.Normal := by
  by_contra hn
  have hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G) := by
    refine ⟨?_,hG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 G) pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  obtain ⟨hi,hm⟩ := (proposition_1_2_1_three_index_knownSimple hQ hJ).resolve_left hn
  let := simple_of_three_dvd_model hm hd
  have hr := nonnormal_component_threeResidual hJ hi hd
    (hG.stronglyQuasithin 3 (by decide) (by decide)) hm
  have hres : primeToResidual 3 G ≤ H := by
    rw [hr]
    exact conjugateSpanBy_le hJH (by rw [normalizer_eq_top])
  apply hout
  apply hres
  apply mem_primeToResidual_of_pow (n := 1)
  simpa only [pow_one, hx] using pow_orderOf_eq_one x
omit [Finite G] in
/-- The sole three-free row in the actual nonnormal component catalogue. -/
theorem NonnormalCComponentModel.suzuki_of_three_free
    (hm : NonnormalCComponentModel G) (hd : ¬ 3 ∣ Nat.card G) :
    ∃ m, 1 ≤ m ∧ Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  cases hm with
  | linear_even n hn he =>
    obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := he
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    have h := Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
      (F := F) (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
    exact (hd (by rw [Nat.card_congr e.toEquiv]; exact h.trans (card_subgroup_dvd_card _))).elim
  | linear_prime p hp ho he =>
    obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := he
    exact (hd (Theory.PSL2.prime_model_three_dvd_card hp ho hcard e)).elim
  | suzuki m hm he => exact ⟨m,hm,he⟩
  | janko he =>
    obtain ⟨e⟩ := he
    apply False.elim
    apply hd
    rw [Nat.card_congr e.toEquiv]
    exact Janko1.orderOf_b ▸ orderOf_dvd_natCard Janko1.b

/-- The remaining nonnormal alternative retains its actual Suzuki quotient. -/
theorem component_normal_or_suzuki_of_cubic_outside_normal
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (H : Subgroup G) [H.Normal] {J : Subgroup G} (hJ : J.IsCComponent)
    [IsQuasisimple (J ⧸ pCore 2 J)] (hJH : J ≤ H)
    (x : G) (hx : orderOf x = 3) (hout : x ∉ H) :
    J.Normal ∨ ∃ m, 1 ≤ m ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  by_cases hn : J.Normal
  · exact Or.inl hn
  · right
    have hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G) := by
      refine ⟨?_,hG.isKGroup.quotient _⟩
      intro p hp ho
      let : Fact p.Prime := ⟨hp⟩
      exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 G) pCore_isPGroup).trans
        (hG.stronglyQuasithin p hp ho)
    obtain ⟨_,hm⟩ := (proposition_1_2_1_three_index_knownSimple hQ hJ).resolve_left hn
    exact hm.suzuki_of_three_free (fun hd => hn
      (component_normal_of_cubic_outside_normal hG H hJ hJH hd x hx hout))

end CFSG.Quasithin.Chapter1.Section02
