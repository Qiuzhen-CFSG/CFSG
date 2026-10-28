module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveModelsInputs
public import Theory.GroupTheory.CComponent.PrimeRankOuterTwo
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveSectionTernarySieve
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.AlternatingCubics

/-!
This additive source variant uses `SecondaryActionData` and preserves the
full quotient and central-cover hypotheses without universal radical movement.

# The outer-two model branches of the nonblock prime-rank sieve

An actual torus element of order p lies outside the normal C-component.
The coprime-center absorption theorem therefore forces p-rank one whenever
the full component quotient has a two-group outer automorphism group.
This proves the restriction for all alternating, odd PSL₂, binary
higher-linear and centerless sporadic Theorem C rows. Both alternating
triple covers are treated as full covers: their cubic actors are absorbed
by the existing exponent-three calculations, and every other prime uses
their actual center of order three and outer two-group.

In the centerless rank-two case, the source catalogue now leaves only
odd ternary or characteristic-two Lie models. This is an intermediate
restriction, not the complete A.3.18 dichotomy or 4.3.16 list. Its remaining
model analysis and final assembly belong to qt-d-1222-nonblock-endgame-sieve.
Source: Aschbacher–Smith, A.3.18, pp.51–53, and original 4.3.12(2), p.617.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Chapter1.XiEmbedding.OuterModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The outer-two branch of the source prime-rank restriction. -/
theorem SecondaryActionData.component_primeRank_eq_one_of_outer_two (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hz : Nat.Coprime p (Nat.card (center (s.component ⧸ pCore 2 s.component))))
    (hout : IsPGroup 2 (MulAut.Outer (s.component ⧸ pCore 2 s.component))) :
    primeRank p s.component = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let := s.normal
  obtain ⟨a, _, ha, han⟩ := SecondaryActionData.exists_outside_prime_actor s hp hd
  have hu := CComponentPrimeRank.rank_le_one_of_outside_prime_actor
    s.component s.isComponent hz ((rootNormalizer_sqtk c D h).stronglyQuasithin p hp ho)
    ho hout a ha han
  have hl := Theory.GroupTheory.primeRank_le_of_injective p (SecondaryActionData.secondaryToComponent s)
    (SecondaryActionData.secondaryToComponent_injective s)
  rw [SecondaryActionData.secondary_primeRank_eq_one s hp ho hd] at hl
  omega

/-- Rank two at a torus prime forces an odd outer automorphism whenever
the full component quotient has p-prime center. -/
theorem SecondaryActionData.outer_not_two_of_rank_two (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hz : Nat.Coprime p (Nat.card (center (s.component ⧸ pCore 2 s.component))))
    (hr : 2 ≤ primeRank p s.component) :
    ¬ IsPGroup 2 (MulAut.Outer (s.component ⧸ pCore 2 s.component)) := by
  intro hout
  have he := SecondaryActionData.component_primeRank_eq_one_of_outer_two s D h hp ho hd hz hout
  omega

private theorem alternating_outer_two (m : ℕ) (hm : 5 ≤ m) :
    IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin m))) := by
  by_cases he : m = 6
  · subst m
    exact IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card
  let A := alternatingGroup (Fin m)
  let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hc : Nat.card (Equiv.Perm (Fin m) ⧸ A) = 2 ^ 1 := by
    rw [← A.index_eq_card]
    exact alternatingGroup.index_eq_two
  apply (IsPGroup.of_card hc).of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨σ, rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m hm he).surjective a
  exact ⟨QuotientGroup.mk' A σ, rfl⟩

private theorem two_transfer {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : IsPGroup 2 (MulAut.Outer B)) : IsPGroup 2 (MulAut.Outer A) :=
  h.of_equiv (MulAut.outerCongr e).symm

/-- All alternating rows satisfy the rank-one restriction. -/
theorem SecondaryActionData.component_primeRank_eq_one_of_alternating (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p m : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hm : 5 ≤ m) (e : (s.component ⧸ pCore 2 s.component) ≃* alternatingGroup (Fin m)) :
    primeRank p s.component = 1 := by
  apply SecondaryActionData.component_primeRank_eq_one_of_outer_two s D h hp ho hd
    ?_ (two_transfer e (alternating_outer_two m hm))
  rw [Nat.card_congr (centerCongr e).toEquiv,
    alternatingGroup.center_eq_bot (by simp; omega)]
  simp

private theorem sporadic_outer_two {J : Type*} [Group J] [IsSimpleGroup J]
    (hm : ChapterA.Section02.IsTheoremCSporadicModel J) : IsPGroup 2 (MulAut.Outer J) := by
  rcases hm with ⟨name, hne, ⟨e⟩⟩ | ⟨e⟩
  · cases name with
    | m11 => exact two_transfer e Sporadic.Mathieu.m11_outer_isPGroup_two
    | m12 => exact two_transfer e (m12_outer_isPGroup_two_of_sylow_aut
        Sporadic.Mathieu.M12SmallPair.SylowAutomorphismGroup.isPGroup_two)
    | m22 => exact two_transfer e (m22_outer_isPGroup_two_of_coverage
        Sporadic.Mathieu.m22DesignAutToAut_surjective)
    | m23 => exact two_transfer e Sporadic.Mathieu.m23_outer_isTwoGroup
    | m24 => exact two_transfer e Sporadic.Mathieu.M24OuterRestriction.outer_isPGroup_two
    | j2 => exact two_transfer e JankoTwo.outer_isPGroup_two
    | hs => exact two_transfer e (Sporadic.LeechRelated.HS.outer_isPGroup_two_of_pointStabilizer_map
        Sporadic.LeechRelated.HS.pointStabilizer_map
        Sporadic.LeechRelated.HS.normalizer_relIndex_dvd_two_pow)
    | ru =>
      let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
      let := rudvalis_outer_subsingleton
      have ho : IsPGroup 2 (MulAut.Outer Rudvalis.Model) := IsPGroup.of_subsingleton 2 _
      exact two_transfer e ho
    | j3 => exact (hne rfl).elim
    | he => exact two_transfer e (Subgroup.isPGroup_outer_of_normalizer
        Held.permutationGroup 2 Held.Realization.normalizer_surjective
        Held.isPGroup_permutationNormalizerQuotient)
    | j4 => exact two_transfer e Janko4.AdequateLocal.outer_isPGroup_two
  · obtain ⟨e⟩ := e
    let := Janko1.OuterCertificate.outer_subsingleton
    have ho : IsPGroup 2 (MulAut.Outer Janko1.Model) := IsPGroup.of_subsingleton 2 _
    exact two_transfer e ho

private theorem simple_of_center_bot {J : Type*} [Group J] [IsQuasisimple J]
    (hz : center J = ⊥) : IsSimpleGroup J := by
  let : IsSimpleGroup (J ⧸ center J) := IsQuasisimple.simple
  exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup

/-- All centerless sporadic rows of Theorem C satisfy the rank-one restriction. -/
theorem SecondaryActionData.component_primeRank_eq_one_of_sporadic (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hz : center (s.component ⧸ pCore 2 s.component) = ⊥)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel (s.component ⧸ pCore 2 s.component)) :
    primeRank p s.component = 1 := by
  let := s.quasisimple
  let := simple_of_center_bot hz
  exact SecondaryActionData.component_primeRank_eq_one_of_outer_two s D h hp ho hd
    (by rw [hz]; simp) (sporadic_outer_two hm)

/-- The centerless full quotient itself has the source Theorem C model. -/
theorem SecondaryActionData.componentQuotient_theoremC_of_center_bot (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hz : center (s.component ⧸ pCore 2 s.component) = ⊥) :
    ChapterA.Section02.IsTheoremCModel (s.component ⧸ pCore 2 s.component) := by
  let := s.quasisimple
  let := simple_of_center_bot hz
  have hs := SecondaryActionData.componentQuotient_sqtk s D h
  exact ChapterA.Section02.theoremC_knownSimple inferInstance
    (Group.IsPerfect.not_isMulCommutative _) hs.stronglyQuasithin hs.isKGroup

/-- Odd-characteristic PSL₂ rows in Theorem C have outer two-groups. -/
theorem SecondaryActionData.component_primeRank_eq_one_of_odd_linear_two (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p r k : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hr : r.Prime) (hor : Odd r) (hk : k ≤ 2)
    (hm : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 2 (r ^ k)) :
    primeRank p s.component = 1 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  apply SecondaryActionData.component_primeRank_eq_one_of_outer_two s D h hp ho hd
    ?_ (two_transfer e (Theory.PSL2.OuterSolvable.SmallDegreeSquares.outer_isPGroup_two hr hor hk hF))
  rw [Nat.card_congr (centerCongr e).toEquiv, GorensteinWalter.psl2_center_eq_bot]
  simp

/-- The dimension-four and dimension-five binary rows satisfy the rank-one restriction. -/
theorem SecondaryActionData.component_primeRank_eq_one_of_binary_linear (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p m : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hm : m = 4 ∨ m = 5)
    (hmodel : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) m 2) :
    primeRank p s.component = 1 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  let a := (e.trans (Atlas.fieldEquivPSL m eF)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < m))
  apply SecondaryActionData.component_primeRank_eq_one_of_outer_two s D h hp ho hd
    ?_ (two_transfer a (Theory.SpecificGroups.BinaryComponentResidual.linear_outer_two hm))
  rw [Nat.card_congr (centerCongr a).toEquiv,
    BinaryLinear.OuterCyclic.binary_center_eq_bot (by omega)]
  simp

/-- An outside cubic torus element excludes both exceptional alternating
three-covers on the full component quotient. -/
theorem SecondaryActionData.not_alternating_cover_of_three_dvd (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd : 3 ∣ 2 ^ n - 1) :
    ¬ (Chapter1.Section02.LocalModels.IsAlternatingCover (s.component ⧸ pCore 2 s.component) 6 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover (s.component ⧸ pCore 2 s.component) 7) := by
  let := s.quasisimple
  let := s.normal
  obtain ⟨a, _, ha, han⟩ := SecondaryActionData.exists_outside_prime_actor s Nat.prime_three hd
  have hr := (rootNormalizer_sqtk c D h).stronglyQuasithin 3 Nat.prime_three (by decide)
  have hnorm : a ∈ normalizer (s.component : Set (rootNormalizer c)) := by
    rw [normalizer_eq_top]
    trivial
  rintro (⟨_, ⟨ez⟩, ⟨eq⟩⟩ | ⟨_, ⟨ez⟩, ⟨eq⟩⟩)
  · have hc : Nat.card (center (s.component ⧸ pCore 2 s.component)) = 3 :=
      (Nat.card_congr ez.toEquiv).trans (by simp)
    obtain ⟨e⟩ := GLS3.Chapter5.OddCentralCovers.triple_six_equiv_hexacode eq hc
    exact han (HexacodeTheta.order_three_mem s.component s.isComponent e hr ha hnorm)
  · have hc : Nat.card (center (s.component ⧸ pCore 2 s.component)) = 3 :=
      (Nat.card_congr ez.toEquiv).trans (by simp)
    obtain ⟨e⟩ := GLS3.Chapter5.OddCentralCovers.triple_seven_equiv eq hc
    exact han (TripleSevenTheta.order_three_mem s.component s.isComponent e hr ha hnorm)

/-- The two alternating central covers satisfy the rank-one restriction
at every source torus prime; the cubic case itself is impossible. -/
theorem SecondaryActionData.component_primeRank_eq_one_of_alternating_cover (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hm : Chapter1.Section02.LocalModels.IsAlternatingCover (s.component ⧸ pCore 2 s.component) 6 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover (s.component ⧸ pCore 2 s.component) 7) :
    primeRank p s.component = 1 := by
  let := s.quasisimple
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact SecondaryActionData.not_alternating_cover_of_three_dvd s D h hd hm
  rcases hm with ⟨_, ⟨ez⟩, ⟨eq⟩⟩ | ⟨_, ⟨ez⟩, ⟨eq⟩⟩
  all_goals
    have hc : Nat.card (center (s.component ⧸ pCore 2 s.component)) = 3 :=
      (Nat.card_congr ez.toEquiv).trans (by simp)
    have hcop : Nat.Coprime p (Nat.card (center (s.component ⧸ pCore 2 s.component))) := by
      rw [hc]
      exact hp.coprime_iff_not_dvd.mpr (fun hd =>
        hp3 (((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left hp.ne_one))
    apply SecondaryActionData.component_primeRank_eq_one_of_outer_two s D h hp ho hd hcop
  · obtain ⟨e⟩ := GLS3.Chapter5.OddCentralCovers.triple_six_equiv_hexacode eq hc
    exact two_transfer e Representation.Hexacode.even_outer_two
  · obtain ⟨e⟩ := GLS3.Chapter5.OddCentralCovers.triple_seven_equiv eq hc
    exact two_transfer e GLS3.Chapter5.OddCentralCovers.tripleSeven_outer_two

/-- The centerless rank-two branch has only Lie-type models with possible odd
outer automorphisms. This is an intermediate A.3.18 sieve, not its conclusion. -/
theorem SecondaryActionData.centerless_rank_two_models (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1)
    (hz : center (s.component ⧸ pCore 2 s.component) = ⊥)
    (hr : 2 ≤ primeRank p s.component) :
    (∃ r : ℕ, r.Prime ∧ Odd r ∧
      (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 r ∨
        ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 r)) ∨
      ClassificationModels.IsBenderModel (s.component ⧸ pCore 2 s.component) ∨
        Chapter1.Section02.LocalModels.RankTwoTheoremC (s.component ⧸ pCore 2 s.component) := by
  let := s.quasisimple
  let := simple_of_center_bot hz
  have hm := ChapterA.Section03.SourceComponents.sourceTheoremC_to_local
    (Group.IsPerfect.not_isMulCommutative (s.component ⧸ pCore 2 s.component))
    (SecondaryActionData.componentQuotient_theoremC_of_center_bot s D h hz)
  cases hm with
  | alternating m hm he =>
    have he := SecondaryActionData.component_primeRank_eq_one_of_alternating s D h hp ho hd hm.1 he.some
    omega
  | linear_odd r k hprime hodd hk _ he =>
    have he := SecondaryActionData.component_primeRank_eq_one_of_odd_linear_two s D h hp ho hd
      hprime hodd (by omega) he
    omega
  | three_odd r hprime hodd unitary he =>
    refine Or.inl ⟨r, hprime, hodd, ?_⟩
    cases unitary
    · exact Or.inl he
    · exact Or.inr he
  | rank_one he => exact Or.inr (Or.inl he)
  | rank_two he => exact Or.inr (Or.inr he)
  | binary_linear m hm he =>
    have he := SecondaryActionData.component_primeRank_eq_one_of_binary_linear s D h hp ho hd hm he
    omega
  | sporadic name hne he =>
    have he := SecondaryActionData.component_primeRank_eq_one_of_sporadic s D h hp ho hd hz
      (Or.inl ⟨name, hne, he⟩)
    omega
  | janko_one he =>
    have he := SecondaryActionData.component_primeRank_eq_one_of_sporadic s D h hp ho hd hz (Or.inr he)
    omega
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
