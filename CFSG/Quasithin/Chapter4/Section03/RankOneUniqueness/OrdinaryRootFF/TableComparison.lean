module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF.CoreQuotient
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF.ImageComparison
public import Theory.SpecificGroups.Classical.BinaryFiveRanks
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow

/-!
# The ordinary-root action table at cubic rank one

Inspect the corrected B.5.1 and B.4.2 action tables using actual cubic-rank
witnesses. Cubic rank at most one leaves the natural SL₂ row, the small
orthogonal row with actor A₅, and natural or doubled SL₃ over an odd binary
degree. The first two rows give equality with the original embedded point
image. In either SL₃ row, divisibility of group orders forces the source
degree to be odd: an even-degree SL₂ has order divisible by five, whereas
an odd-degree binary SL₃ does not.

Consequently every even-degree low-cubic-rank configuration satisfies both
terminal group conclusions and the literal root contradiction. Applied
without a rank premise, this reduces the even-degree branch to the actual
signed projective cubic actor from A.3.18, with trivial center and no binary
SL₃ marking. Excluding that remaining actor, and comparing the rows for the
other Cartan primes, are still obligations of the full source assembly.

Source: Aschbacher–Smith 4.3.6, printed p.615; B.4.2 and B.5.1,
printed pp.86 and 99–103; A.3.18, printed pp.51–53.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
open ChapterB.QuasisimpleSource

private theorem threeRank_le_one_of_surjective
    {H E : Type*} [Group H] [Finite H] [Group E] [Finite E]
    (hr : primeRank 3 H ≤ 1) (f : H →* E) (hf : Function.Surjective f) :
    primeRank 3 E ≤ 1 := by
  let P : Sylow 3 H := Classical.choice inferInstance
  exact P.primeRank_le_one_of_surjective
    (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr) f hf

private theorem not_binary_higher_of_threeRank
    {H : Type*} [Group H] [Finite H] (hr : primeRank 3 H ≤ 1)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (e : H ≃* SL(d,ZMod 2)) : False := by
  have he : primeRank 3 SL(d,ZMod 2) ≤ 1 := by rwa [← primeRank_congr 3 e]
  rcases hd with rfl | rfl
  · rw [primeRank_congr 3 (Atlas.Order20160A8.sl4TwoEquivPSL.trans
        Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm)] at he
    have hb := alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide : 6 ≤ 8)
    omega
  · have hb := Theory.SpecificGroups.Classical.BinaryFiveRanks.projective_threeRank_ge_two
    have hq := threeRank_le_one_of_surjective he (QuotientGroup.mk' (center SL(5,ZMod 2)))
      (QuotientGroup.mk'_surjective _)
    change primeRank 3 PSL(5,ZMod 2) ≤ 1 at hq
    omega

private theorem not_alternating_of_threeRank
    {H : Type*} [Group H] [Finite H] (hr : primeRank 3 H ≤ 1)
    {d : ℕ} (hd : 6 ≤ d) (e : H ≃* alternatingGroup (Fin d)) : False := by
  have hb := alternatingGroup.TwoThreeCycles.two_le_primeRank hd
  rw [← primeRank_congr 3 e] at hb
  omega

private theorem linearThree_degree_odd_of_threeRank
    {H : Type*} [Group H] [Finite H] (hr : primeRank 3 H ≤ 1)
    (F : BinaryField) (e : H ≃* SL(3,F.Carrier)) : Odd F.degree := by
  by_contra hn
  have he := Nat.not_odd_iff_even.mp hn
  have hd : 3 ∣ Nat.card F.Carrier - 1 := by
    rw [F.card_eq]
    exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff _).mpr he
  have hb := Matrix.PSL3.SplitPrimeRank.special_rank F.Carrier hd
  rw [← primeRank_congr 3 e] at hb
  omega

/-- The source rows surviving the cubic rank restriction, retaining the
actual natural and doubled-natural action equivalences. -/
def RankOneRows {H X : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X) (s : MovedSection ρ ⊤) : Prop :=
  (∃ (F : BinaryField)
      (_e : ActionEquiv (s.action.comp (⊤ : Subgroup H).subtype) (linearNatural F 2)),
      ∀ A, IsBestOffender s.action A → ∃ S : Sylow 2 (⊤ : Subgroup H),
        A = (S : Subgroup (⊤ : Subgroup H)).map (⊤ : Subgroup H).subtype) ∨
  Nonempty ((⊤ : Subgroup H) ≃* alternatingGroup (Fin 5)) ∨
  (∃ (F : BinaryField), Odd F.degree ∧
      Nonempty (ActionEquiv (s.action.comp (⊤ : Subgroup H).subtype) (linearNatural F 3))) ∨
  (∃ (F : BinaryField), Odd F.degree ∧
      Nonempty (ActionEquiv (s.space.toRepresentation.comp (⊤ : Subgroup H).subtype)
        (repeated (linearNatural F 3) 2)))

/-- Inspect all rows of the source-correct B.4.2 and B.5.1 tables. -/
theorem rankOneRows_of_source
    {H X : Type*} [Group H] [Finite H] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X)
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ ⊤)
    (hr : primeRank 3 H ≤ 1) : RankOneRows ρ c.sectionData := by
  have hrTop : primeRank 3 (⊤ : Subgroup H) ≤ 1 := by
    rwa [primeRank_congr 3 (topEquiv : (⊤ : Subgroup H) ≃* H)]
  cases c.clause_one with
  | doubleThree F _ e _ _ =>
    exact Or.inr (Or.inr (Or.inr ⟨F,linearThree_degree_odd_of_threeRank hrTop F e.groupEquiv,⟨e⟩⟩))
  | naturalDual d hd _ e =>
    exact (not_binary_higher_of_threeRank hrTop hd e.some.groupEquiv).elim
  | repeatedNatural d r hd _ _ _ e =>
    exact (not_binary_higher_of_threeRank hrTop hd e.some.groupEquiv).elim
  | irreducible _ _ _ hs _ =>
    cases hs with
    | linearTwo F _ e ha _ => exact Or.inl ⟨F,e,ha⟩
    | linearThree F _ e _ =>
      exact Or.inr (Or.inr (Or.inl ⟨F,linearThree_degree_odd_of_threeRank hrTop F e.groupEquiv,⟨e⟩⟩))
    | symplectic F _ _ e _ =>
      have hb := Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic (F := F.Carrier)
      have hi := Theory.GroupTheory.primeRank_le_of_injective 3
        (commutator (Matrix.symplecticGroup (Fin 2) F.Carrier)).subtype
        (commutator _).subtype_injective
      rw [← primeRank_congr 3 e.groupEquiv] at hi
      omega
    | symplecticTwo e _ =>
      have hb := Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic (F := ZMod 2)
      rw [← primeRank_congr 3 e.subgroupEquiv] at hb
      omega
    | g2 F _ _ e _ _ =>
      have hb := Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2 (F := F.Carrier)
      have hi := Theory.GroupTheory.primeRank_le_of_injective 3 (commutator (Atlas.G2.Model F.Carrier)).subtype
        (commutator _).subtype_injective
      rw [← primeRank_congr 3 e.groupEquiv] at hi
      omega
    | g2Two e _ _ =>
      have hb := Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2 (F := ZMod 2)
      rw [← primeRank_congr 3 e.subgroupEquiv] at hb
      omega
    | symmetric d hd e _ _ =>
      rcases hd with rfl | rfl
      · exact Or.inr (Or.inl ⟨e.subgroupEquiv⟩)
      · exact (not_alternating_of_threeRank hrTop (by decide) e.subgroupEquiv).elim
    | alternatingSix _ e _ _ =>
      exact (not_alternating_of_threeRank hrTop (by decide) e.groupEquiv).elim
    | alternatingSeven _ _ e _ _ _ =>
      exact (not_alternating_of_threeRank hrTop (by decide) e).elim
    | tripleSix _ a _ =>
      have hb := threeRank_le_one_of_surjective hrTop
        (a.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (center (⊤ : Subgroup H))))
        (a.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
      have hl := alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide : 6 ≤ 6)
      omega
    | binaryLinear d hd _ e _ =>
      exact (not_binary_higher_of_threeRank hrTop hd e.groupEquiv).elim
    | orthogonalSix _ _ e _ _ =>
      exact (not_alternating_of_threeRank hrTop (by decide) e.groupEquiv).elim
    | symmetricEight _ e _ =>
      exact (not_alternating_of_threeRank hrTop (by decide) e.subgroupEquiv).elim
    | exteriorFive _ _ e _ _ _ =>
      exact (not_binary_higher_of_threeRank hrTop (Or.inr rfl) e).elim

private theorem five_not_dvd_linearThree_odd (F : BinaryField) (ho : Odd F.degree) :
    ¬ 5 ∣ Nat.card SL(3,F.Carrier) := by
  rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,F.card_eq]
  intro hd
  have hq : 1 ≤ 2 ^ F.degree := Nat.one_le_pow _ _ (by decide)
  have h2 : 1 ≤ (2 ^ F.degree) ^ 2 := Nat.one_le_pow _ _ hq
  have h3 : 1 ≤ (2 ^ F.degree) ^ 3 := Nat.one_le_pow _ _ hq
  have hz := (ZMod.natCast_eq_zero_iff _ 5).mpr hd
  push_cast [Nat.cast_sub h2,Nat.cast_sub h3] at hz
  rw [pow_eq_pow_mod _ (by decide : (2 : ZMod 5)^4=1)] at hz
  have hm2 := Nat.odd_iff.mp ho
  have hm : F.degree % 4 = 1 ∨ F.degree % 4 = 3 := by omega
  rcases hm with hm | hm <;> rw [hm] at hz <;> revert hz <;> decide

private theorem five_dvd_linearTwo_even
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Even n) : 5 ∣ Nat.card SL(2,F) := by
  rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,hF]
  apply (ZMod.natCast_eq_zero_iff _ 5).mp
  have hq : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by decide)
  have h2 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ hq
  push_cast [Nat.cast_sub h2]
  rw [pow_eq_pow_mod _ (by decide : (2 : ZMod 5)^4=1)]
  have hm2 := Nat.even_iff.mp hn
  have hm : n % 4 = 0 ∨ n % 4 = 2 := by omega
  rcases hm with hm | hm <;> rw [hm] <;> decide

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} (m : OrdinarySymplecticMarking c n)

/-- The small orthogonal row gives equality of the original embedded images. -/
theorem image_eq_of_card_le_sixty (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hJK : m.second ≤ KZ)
    (hsmall : Nat.card (image m KZ) ≤ 60) : image m KZ = image m m.second := by
  have hj : 60 ≤ Nat.card (image m m.second) := by
    rw [Nat.card_congr (secondImageEquiv m hn hr hUN hcore).toEquiv,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,m.card]
    have hq : 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn
    calc
      60 = 4 * (4 ^ 2 - 1) := by norm_num
      _ ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by gcongr
  exact (eq_of_le_of_card_ge (image_mono m hJK) (hsmall.trans hj)).symm

omit [Finite G] in
/-- An embedded SL₂ over an even binary degree cannot lie in an SL₃
row of odd binary degree: five divides the former order but not the latter. -/
theorem degree_odd_of_linearThree_image (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hJK : m.second ≤ KZ)
    (F : BinaryField) (hF : Odd F.degree) (e : image m KZ ≃* SL(3,F.Carrier)) : Odd n := by
  apply Nat.not_even_iff_odd.mp
  intro he
  have hd : 5 ∣ Nat.card (image m m.second) := by
    rw [Nat.card_congr (secondImageEquiv m hn hr hUN hcore).toEquiv]
    exact five_dvd_linearTwo_even m.card he
  have hi := card_dvd_of_le (image_mono m hJK)
  rw [Nat.card_congr e.toEquiv] at hi
  exact five_not_dvd_linearThree_odd F hF (hd.trans hi)

/-- Apply the reduced table at the original embedded point image. -/
theorem image_eq_or_linearThree_of_rows (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hJK : m.second ≤ KZ)
    (s : letI := hr.elementary
      MovedSection ((representation m hr).comp (image m KZ).subtype) ⊤)
    (hrows : letI := hr.elementary
      RankOneRows ((representation m hr).comp (image m KZ).subtype) s) :
    letI := hr.elementary
    image m KZ = image m m.second ∨ Odd n ∧
      ∃ (s : MovedSection ((representation m hr).comp (image m KZ).subtype) ⊤)
        (F : BinaryField), Odd F.degree ∧
        (Nonempty (ActionEquiv (s.action.comp (⊤ : Subgroup (image m KZ)).subtype)
          (linearNatural F 3)) ∨
         Nonempty (ActionEquiv (s.space.toRepresentation.comp (⊤ : Subgroup (image m KZ)).subtype)
          (repeated (linearNatural F 3) 2))) := by
  let := hr.elementary
  rcases hrows with ⟨F,e,ha⟩ | he | ⟨F,ho,⟨e⟩⟩ | ⟨F,ho,⟨e⟩⟩
  ·
    exact Or.inl (image_eq_of_linearTwo_section m hn hr hUN hcore hQ KZ hJK s F e ha)
  ·
    obtain ⟨e⟩ := he
    left
    apply image_eq_of_card_le_sixty m hn hr hUN hcore KZ hJK
    rw [← Nat.card_congr (topEquiv : (⊤ : Subgroup (image m KZ)) ≃* image m KZ).toEquiv,
      Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num
  ·
    exact Or.inr ⟨degree_odd_of_linearThree_image m hn hr hUN hcore KZ hJK F ho
      (topEquiv.symm.trans e.groupEquiv),s,F,ho,Or.inl ⟨e⟩⟩
  ·
    exact Or.inr ⟨degree_odd_of_linearThree_image m hn hr hUN hcore KZ hJK F ho
      (topEquiv.symm.trans e.groupEquiv),s,F,ho,Or.inr ⟨e⟩⟩

/-- The cubic rank bound reduces the full source table to equality of the
original images or an odd-degree SL₃ action on the actual moved section. -/
theorem image_eq_or_linearThree_of_threeRank (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hKN : KZ ≤ m.rootNormalizer) (hJK : m.second ≤ KZ)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hthree : primeRank 3 (image m KZ) ≤ 1) :
    letI := hr.elementary
    image m KZ = image m m.second ∨ Odd n ∧
      ∃ (s : MovedSection ((representation m hr).comp (image m KZ).subtype) ⊤)
        (F : BinaryField), Odd F.degree ∧
        (Nonempty (ActionEquiv (s.action.comp (⊤ : Subgroup (image m KZ)).subtype)
          (linearNatural F 3)) ∨
         Nonempty (ActionEquiv (s.space.toRepresentation.comp (⊤ : Subgroup (image m KZ)).subtype)
          (repeated (linearNatural F 3) 2))) := by
  let := hr.elementary
  obtain ⟨s⟩ := secondary_source_classification m hn h hr hUN hcore hQ KZ hKN hJK hquasi hnormal
  exact image_eq_or_linearThree_of_rows m hn hr hUN hcore hQ KZ hJK s.sectionData
    (rankOneRows_of_source _ s hthree)

/-- For even source degree, the cubic rank bound closes every table row. -/
theorem image_eq_of_even_threeRank (hn : 1 < n) (he : Even n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hKN : KZ ≤ m.rootNormalizer) (hJK : m.second ≤ KZ)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hthree : primeRank 3 (image m KZ) ≤ 1) : image m KZ = image m m.second := by
  let := hr.elementary
  rcases image_eq_or_linearThree_of_threeRank m hn h hr hUN hcore hQ KZ hKN hJK hquasi hnormal
    hthree with heq | ⟨ho,_⟩
  · exact heq
  · exact (Nat.not_even_iff_odd.mpr ho he).elim

/-- The even-degree table comparison discharges both terminal group premises. -/
theorem module_and_containment_of_even_threeRank (hn : 1 < n) (he : Even n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hseed : conjugateSpanBy c.ordinaryModule m.second = m.second)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hKN : KZ ≤ m.rootNormalizer)
    (hKZ : conjugateSpanBy m.second KZ = KZ)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hthree : primeRank 3 (image m KZ) ≤ 1) :
    m.rootSpan = m.second.pCoreIn 2 ∧ KZ ≤ m.second ⊔ m.rootCore :=
  module_and_containment_of_image_eq m hn hr hUN hcore hseed hQ KZ hKN hKZ hquasi hnormal
    (image_eq_of_even_threeRank m hn he h hr hUN hcore hQ KZ hKN
      ((le_conjugateSpanBy _ _).trans_eq hKZ) hquasi hnormal hthree)

/-- Literal source consumer for every even-degree low-cubic-rank row. -/
theorem false_of_even_threeRank
    (D : Chapter12.Section02.ChosenModule T L V) (hn : 1 < n) (he : Even n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hT : (T : Subgroup G) ≤ m.rootNormalizer)
    (hseed : conjugateSpanBy c.ordinaryModule m.second = m.second)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hcentral : KZ ≤ centralizer (m.root : Set G))
    (hKZ : conjugateSpanBy m.second KZ = KZ)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hthree : primeRank 3 (image m KZ) ≤ 1) : False := by
  obtain ⟨hU,hle⟩ := module_and_containment_of_even_threeRank m hn he h hr hUN hcore hseed hQ
    KZ (hcentral.trans (Subgroup.centralizer_le_normalizer _)) hKZ hquasi hnormal hthree
  exact c.ordinary_false_of_root_module D hn m KZ hT hseed hU hQ hKZ hle hnormal

open Chapter1.Section02.LocalModels ChapterA.Section03.OddPrime.SourceModels in
/-- Without an extra rank premise, the original even-degree configuration
forces precisely the outstanding projective cubic exception on its actual
faithful actor. Every binary SL₃ marking of this actor is impossible. -/
theorem even_degree_projective_obstruction
    (D : Chapter12.Section02.ChosenModule T L V) (hn : 1 < n) (he : Even n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hT : (T : Subgroup G) ≤ m.rootNormalizer)
    (hseed : conjugateSpanBy c.ordinaryModule m.second = m.second)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hcentral : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hKZ : conjugateSpanBy m.second KZ = KZ)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G)) :
    center (image m KZ) = ⊥ ∧ 1 < primeRank 3 (image m KZ) ∧
      (∃ (unitary : Bool) (q : ℕ), SignedCongruence unitary q ∧
        IsPSLSign (image m KZ) unitary 3 q) ∧
      ∀ F : BinaryField, ¬ Nonempty (image m KZ ≃* SL(3,F.Carrier)) := by
  have hJK : m.second ≤ KZ := (le_conjugateSpanBy _ _).trans_eq hKZ
  have hd := (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr he
  have hhigh : 1 < primeRank 3 KZ := by
    by_contra! hlo
    have hi := threeRank_le_one_of_surjective hlo
      (secondaryProjection m KZ (hcentral.trans (Subgroup.centralizer_le_normalizer _)))
      (secondaryProjection_surjective m KZ _)
    exact false_of_even_threeRank m D hn he h hr hUN hcore hT hseed hQ KZ hcentral
      hKZ hquasi hnormal hi
  obtain ⟨hz,hhi,hproj⟩ := secondary_image_projective_of_high_three_rank m hn h hr hUN hcore
    KZ hcentral hJK hcomp hquasi hnormal hd hhigh
  refine ⟨hz,hhi,hproj,?_⟩
  rintro F ⟨e⟩
  exact secondary_image_not_linearThree_of_high_three_rank m hn h hr hUN hcore KZ hcentral hJK
    hcomp hquasi hnormal hd hhigh F e

/-- Application of the orthogonal-five row to the literal root contradiction. -/
theorem false_of_five_image
    (D : Chapter12.Section02.ChosenModule T L V) (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hT : (T : Subgroup G) ≤ m.rootNormalizer)
    (hseed : conjugateSpanBy c.ordinaryModule m.second = m.second)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hcentral : KZ ≤ centralizer (m.root : Set G))
    (hKZ : conjugateSpanBy m.second KZ = KZ)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (e : image m KZ ≃* alternatingGroup (Fin 5)) : False := by
  apply false_of_image_eq m D hn hr hUN hcore KZ hT hseed hQ hcentral hKZ hquasi hnormal
  apply image_eq_of_card_le_sixty m hn hr hUN hcore KZ
    ((le_conjugateSpanBy _ _).trans_eq hKZ)
  rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
  norm_num

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootFF
