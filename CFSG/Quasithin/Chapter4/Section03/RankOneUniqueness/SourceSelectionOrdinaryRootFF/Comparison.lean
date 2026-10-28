module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionOrdinaryRootFF.Classification
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.SpecificGroups.Classical.BinaryFiveRanks
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.SourceFF
public import CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalRanks
public import Theory.Representation.SL2.PerfectCoreQuotientDegree
public import Theory.Representation.SL2.OffenderFieldDegree
public import Theory.Representation.G2NaturalFaithfulness
public import Theory.SpecificGroups.SymplecticFour.SplitTorusRank
public import Theory.SpecificGroups.PSL3.SplitPrimeRank
public import Theory.AtlasPort.LinearGroups.G2.Torus

/-!
# Comparison in the ordinary root argument before full-normalizer identification

This extension adapts the proofs in OrdinaryRootFF/ImageComparison, TableComparison, CubicExclusion, OddTableComparison, OddFieldComparison, Complete
to OutsideSymplecticMarking. Every actor is the literal original root
normalizer modulo the centralizer of the same full root span. No equality
H = N_G(K), secondary-component identification, or action classification is
added as a hypothesis. The constituent source arguments are documented below.
The final SourceSelectionOrdinaryComplete application discharges these inputs
and feeds the original uniqueness consumer.
-/


/-!
# Comparing the actual images in the natural SL₂ branch

An offender remains an offender on the literal moved section. The natural
SL₂ row of B.4.2 places a best offender inside the full module image and
identifies it with a Sylow subgroup of the secondary image. Thus this Sylow
lies in the embedded point-local image. Both groups are marked SL₂ groups:
the Sylow orders compare their coefficient fields, and the SL₂ order formula
forces equality of the two actual subgroups. No abstract isomorphism alone
is used to lift containment modulo the root core.

The final consumer applies this equality to the original root contradiction.
This closes the natural SL₂ row; the other B.5.1/B.4.2 rows remain to be
excluded by the ordinary-root classification argument.

Source: Aschbacher–Smith 4.3.6, printed p.615; B.4.2(1), printed p.86.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideRootFF

private theorem linearTwo_eq_top_of_contains_sylow
    {H F E : Type*} [Group H] [Finite H]
    [Field F] [Finite F] [CharP F 2] [Field E] [Finite E] [CharP E 2]
    (J : Subgroup H) (eH : H ≃* SL(2,E)) (eJ : J ≃* SL(2,F))
    (P : Sylow 2 H) (hPJ : (P : Subgroup H) ≤ J) : J = ⊤ := by
  have hpc : Nat.card P = Nat.card E := by
    let PE := P.mapSurjective (f := eH.toMonoidHom) eH.surjective
    calc
      Nat.card P = Nat.card PE := Nat.card_congr
        ((P : Subgroup H).equivMapOfInjective eH.toMonoidHom eH.injective).toEquiv
      _ = Nat.card E := Nat.card_congr
        (Matrix.SpecialLinearGroup.sylowEquivAdditive E 2 PE).symm.toEquiv
  have hp : IsPGroup 2 ((P : Subgroup H).subgroupOf J) :=
    P.isPGroup'.of_equiv (subgroupOfEquivOfLe hPJ).symm
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  have hsc : Nat.card S = Nat.card F := by
    let SF := S.mapSurjective (f := eJ.toMonoidHom) eJ.surjective
    calc
      Nat.card S = Nat.card SF := Nat.card_congr
        ((S : Subgroup J).equivMapOfInjective eJ.toMonoidHom eJ.injective).toEquiv
      _ = Nat.card F := Nat.card_congr
        (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 SF).symm.toEquiv
  have hfield : Nat.card E ≤ Nat.card F := by
    rw [← hpc, ← hsc, ← Nat.card_congr (subgroupOfEquivOfLe hPJ).toEquiv]
    exact Nat.card_le_card_of_injective _ (inclusion_injective hS)
  apply eq_of_le_of_card_ge (le_top : J ≤ ⊤)
  rw [Nat.card_congr topEquiv.toEquiv, Nat.card_congr eH.toEquiv,
    Nat.card_congr eJ.toEquiv,
    BenderSuzuki.External.huppert614_card_specialLinearGroup,
    BenderSuzuki.External.huppert614_card_specialLinearGroup]
  gcongr

private theorem exists_section_bestOffender
    {H X : Type*} [Group H] [Finite H] [AddCommGroup X] [Module (ZMod 2) X]
    [Module.Finite (ZMod 2) X]
    {ρ : Representation (ZMod 2) H X} {K : Subgroup H}
    (s : ChapterB.QuasisimpleSource.MovedSection ρ K)
    {A : Subgroup H} (hA : IsOffender ρ A) :
    ∃ B ≤ A, IsBestOffender s.action B := by
  apply IsOffender.exists_bestOffender s.action
  refine ⟨hA.1, ?_⟩
  have hq := fixedCodim_quotient_add_subrepresentation_le s.space.toRepresentation s.central A
  have hs := fixedCodim_subrepresentation_le ρ s.space A
  have ha := hA.2
  change fixedCodim s.action A + _ ≤ _ at hq
  omega

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : OutsideChoice T L} {K0 : Subgroup c.H} {n : ℕ} (m : OutsideSymplecticMarking c K0 n)

/-- The natural source row gives equality inside the original quotient actor. -/
theorem image_eq_of_linearTwo_section (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hJK : m.second ≤ KZ)
    (s : letI := hr.elementary
      ChapterB.QuasisimpleSource.MovedSection
        ((representation m hr).comp (image m KZ).subtype) ⊤)
    (F : ChapterB.QuasisimpleSource.BinaryField)
    (e : letI := hr.elementary
      ChapterB.QuasisimpleSource.ActionEquiv
        (s.action.comp (⊤ : Subgroup (image m KZ)).subtype)
        (ChapterB.QuasisimpleSource.linearNatural F 2))
    (hactors : letI := hr.elementary
      ∀ A, IsBestOffender s.action A → ∃ S : Sylow 2 (⊤ : Subgroup (image m KZ)),
        A = (S : Subgroup (⊤ : Subgroup (image m KZ))).map
          (⊤ : Subgroup (image m KZ)).subtype) :
    image m KZ = image m m.second := by
  let := hr.elementary
  let H := image m KZ
  let J := (image m m.second).subgroupOf H
  have hJH := image_mono m hJK
  have hWH := image_mono m ((m.fullModule_le_second hn).trans hJK)
  let A := (image m c.ordinaryModule).subgroupOf H
  have hA : IsOffender ((representation m hr).comp H.subtype) A :=
    ((fullModule_isBestOffender m hn hr hUN hcore hQ).subgroupOf
      (representation m hr) hWH).isOffender _
  obtain ⟨B,hBA,hB⟩ := exists_section_bestOffender s hA
  obtain ⟨S,hS⟩ := hactors B hB
  let t : (⊤ : Subgroup H) ≃* H := topEquiv
  let P := S.mapSurjective (f := t.toMonoidHom) t.surjective
  have hP : (P : Subgroup H) ≤ J := by
    change (S : Subgroup (⊤ : Subgroup H)).map (⊤ : Subgroup H).subtype ≤ J
    rw [← hS]
    exact hBA.trans (fun _ hx => image_mono m (m.fullModule_le_second hn) hx)
  have he := linearTwo_eq_top_of_contains_sylow J
    (topEquiv.symm.trans e.groupEquiv)
    ((subgroupOfEquivOfLe hJH).trans (secondImageEquiv m hn hr hUN hcore)) P hP
  apply le_antisymm ?_ hJH
  intro x hx
  exact (show (⟨x,hx⟩ : H) ∈ J from he.symm ▸ mem_top _)

/-- The natural SL₂ row discharges both literal terminal group premises. -/
theorem module_and_containment_of_linearTwo_section (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hseed : conjugateSpanBy c.ordinaryModule m.second = m.second)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hKN : KZ ≤ m.rootNormalizer)
    (hKZ : conjugateSpanBy m.second KZ = KZ)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (s : letI := hr.elementary
      ChapterB.QuasisimpleSource.MovedSection
        ((representation m hr).comp (image m KZ).subtype) ⊤)
    (F : ChapterB.QuasisimpleSource.BinaryField)
    (e : letI := hr.elementary
      ChapterB.QuasisimpleSource.ActionEquiv
        (s.action.comp (⊤ : Subgroup (image m KZ)).subtype)
        (ChapterB.QuasisimpleSource.linearNatural F 2))
    (hactors : letI := hr.elementary
      ∀ A, IsBestOffender s.action A → ∃ S : Sylow 2 (⊤ : Subgroup (image m KZ)),
        A = (S : Subgroup (⊤ : Subgroup (image m KZ))).map
          (⊤ : Subgroup (image m KZ)).subtype) :
    m.rootSpan = m.second.pCoreIn 2 ∧ KZ ≤ m.second ⊔ m.rootCore :=
  module_and_containment_of_image_eq m hn hr hUN hcore hseed hQ KZ hKN hKZ hquasi hnormal
    (image_eq_of_linearTwo_section m hn hr hUN hcore hQ KZ
      ((le_conjugateSpanBy _ _).trans_eq hKZ) s F e hactors)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideRootFF
end


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
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideRootFF
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
  {c : OutsideChoice T L} {K0 : Subgroup c.H} {n : ℕ} (m : OutsideSymplecticMarking c K0 n)

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

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideRootFF
end


/-!
# Excluding the projective cubic actor in the ordinary-root argument

A centerless quasisimple faithful FF actor has a faithful irreducible section:
a nontrivial perfect action survives on a section, whose central kernel is
trivial, and fixed codimension cannot increase. On that same section, the
proved linear and unitary recognition theorems exclude the signed projective
three-dimensional families at their diagonal congruences. In odd characteristic,
the defining-prime rank forces field exponent one. In characteristic two,
the linear recognition retains the original field degree and would give a
nontrivial cubic center; unitary recognition has ratio two.

Apply this to the original K_Z action and its literal W offender. The exact
A.3.18/star-to-action comparison already proved in CoreQuotient then excludes
the cubic exception. Every prime dividing the original Cartan order has rank
one in K_Z and at most one in its actual action image. The even-degree table
comparison consequently gives equality with the embedded J image, both
terminal subgroup conclusions, and the original root contradiction without
an extra classification or rank premise. Odd-degree table comparisons remain
with the ordinary-root assembly.

Source: Aschbacher–Smith 4.3.6, printed p.615; A.3.18, pp.51–53;
B.4.2, B.5.1 and B.5.6(1), pp.86,99–105; K.2 and K.3, pp.453–457.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideRootFF
open ChapterB.QuasisimpleSource
open Chapter1.Section02.LocalModels ChapterA.Section03.OddPrime.SourceModels

private theorem faithful_irreducible_ff_section
    {H X : Type*} [Group H] [Finite H] [IsQuasisimple H]
    [AddCommGroup X] [Module (ZMod 2) X] [Module.Finite (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X) (hz : center H = ⊥)
    (hf : Function.Injective ρ) (hff : IsFFModule ρ) :
    ∃ U : Subrepresentation ρ, ∃ N : Subrepresentation U.toRepresentation,
      IsIrreducible N.quotientRepresentation ∧
      Function.Injective N.quotientRepresentation ∧ IsFFModule N.quotientRepresentation := by
  let : Group.IsPerfect (⊤ : Subgroup H) := Group.IsPerfect.ofSurjective
    (f := (topEquiv : (⊤ : Subgroup H) ≃* H).symm.toMonoidHom) topEquiv.symm.surjective
  have hn : ¬ (⊤ : Subgroup H) ≤ ρ.ker := by
    intro ht
    have hb := (MonoidHom.ker_eq_bot_iff ρ).mpr hf
    obtain ⟨A,hA⟩ := hff
    exact hA.1.1 (bot_unique ((le_top.trans ht).trans_eq hb))
  obtain ⟨U,N,hi,hn⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect
    (ρ := ρ) (⊤ : Subgroup H) hn
  have hk : N.quotientRepresentation.ker = ⊥ := by
    rcases IsQuasisimple.normal_le_center_or_eq_top N.quotientRepresentation.ker with hk | ht
    · exact bot_unique (hk.trans_eq hz)
    · exact (hn ht.ge).elim
  refine ⟨U,N,hi,(MonoidHom.ker_eq_bot_iff _).mp hk,?_⟩
  obtain ⟨A,hA⟩ := hff
  refine ⟨A,hA.1,?_⟩
  have hu := fixedCodim_subrepresentation_le ρ U A
  have hn := fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N A
  have ha := hA.2
  omega

private noncomputable def topCenterQuotientEquiv
    {H : Type*} [Group H] (hz : center H = ⊥) :
    ((⊤ : Subgroup H) ⧸ center (⊤ : Subgroup H)) ≃* H :=
  (ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.centralQuotientEquiv
    (topEquiv : (⊤ : Subgroup H) ≃* H)).trans
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot)

private theorem no_signed_projective_irreducible_ff
    {H X : Type*} [Group H] [Finite H] [IsQuasisimple H]
    [AddCommGroup X] [Module (ZMod 2) X] [Module.Finite (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X) (hsq : IsSQTK KnownSimple.IsKnownSimple H)
    (hz : center H = ⊥) (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (hff : IsFFModule ρ) (u : Bool) (q : ℕ) (hq : SignedCongruence u q)
    (hm : IsPSLSign H u 3 q) : False := by
  let : IsSimpleGroup (H ⧸ center H) := IsQuasisimple.simple
  let : Nontrivial H := (QuotientGroup.mk'_surjective (center H)).nontrivial
  let : IsQuasisimple (⊤ : Subgroup H) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have hiTop : IsIrreducible (ρ.comp (⊤ : Subgroup H).subtype) :=
    (irreducible_comp_surjective_iff _ (topEquiv : (⊤ : Subgroup H) ≃* H).surjective ρ).mpr hi
  have hfit : generalizedFitting H = ⊤ := generalizedFitting_eq_top_of_quasisimple
  have hs := ChapterB.SourceClassification.source_hypotheses hsq hfit inferInstance hf hiTop hff
  cases u with
  | false =>
    change ClassicalGroup.IsPSL H 3 q at hm
    change q % 3 = 1 at hq
    have hmTop := hm.of_mulEquiv (topCenterQuotientEquiv hz)
    obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    have hpow : IsPrimePow q := by
      rw [←hcard,Nat.card_eq_fintype_card]
      exact FiniteField.isPrimePow_card F
    obtain ⟨p,r,hp,hr,hpr⟩ := (isPrimePow_nat_iff q).mp hpow
    have hcard' : Nat.card F = p^r := hcard.trans hpr.symm
    let : Fact p.Prime := ⟨hp⟩
    let : CharP F p := charP_of_card_eq_prime_pow (p := p) (f := r) (by
      simpa only [←Nat.card_eq_fintype_card] using hcard')
    by_cases hp2 : p = 2
    · subst p
      obtain ⟨A,hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp hff
      obtain ⟨B,hB,⟨a⟩,_⟩ := ChapterK.Linear.SourceFF.source_of_bestOffender ρ
        hsq hfit.symm inferInstance hf hiTop r hr (hpr ▸ hmTop) A hA
      have hzB : center SL(3,B.Carrier) = ⊥ := by
        apply (eq_bot_iff_card _).mpr
        rw [← Nat.card_congr (centerCongr
          ((topEquiv : (⊤ : Subgroup H) ≃* H).symm.trans a.groupEquiv)).toEquiv,hz]
        simp
      have hnot := (Matrix.SL3.center_eq_bot_iff_card_mod_three B.Carrier).mp hzB
      apply hnot
      rw [B.card_eq,hB,hpr]
      exact hq
    · have hbound : primeRank p PSL(3,F) ≤ 2 := by
        rw [←primeRank_congr p e]
        exact hsq.stronglyQuasithin p hp (hp.odd_of_ne_two hp2)
      have hr1 := ChapterA.Section02.psl3_fieldExponent_eq_one hcard' hr hbound
      have hpq : p = q := by simpa [hr1] using hpr
      exact ChapterB.SourceClassification.not_ff_odd_psl3 hs hp
        (hp.odd_of_ne_two hp2) (hpq ▸ hmTop) hff
  | true =>
    change ClassicalGroup.IsPSU H 3 q at hm
    change q % 3 = 2 at hq
    have hmTop := hm.of_mulEquiv (topCenterQuotientEquiv hz)
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    have hpow2 : IsPrimePow (q^2) := by
      rw [←hcard,Nat.card_eq_fintype_card]
      exact FiniteField.isPrimePow_card F
    have hpow : IsPrimePow q := (isPrimePow_pow_iff (by decide : 2 ≠ 0)).mp hpow2
    obtain ⟨p,r,hp,hr,hpr⟩ := (isPrimePow_nat_iff q).mp hpow
    let : Fact p.Prime := ⟨hp⟩
    by_cases hp2 : p = 2
    · subst p
      by_cases hr1 : r = 1
      · have he : q = 2 := by simpa [hr1] using hpr.symm
        let : Group.IsSolvable (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
          BenderSuzuki.MatrixGroups.HermitianForm.FixedFieldTwo.projective_isSolvable J
            (he ▸ hcard) (he ▸ hconj)
        exact Group.IsPerfect.not_isSolvable H (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
      · exact ChapterB.SourceClassification.not_ff_unitary hs (by omega : 2 ≤ r)
          (hpr ▸ hmTop) hff
    · have hbound : primeRank p (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) ≤ 2 := by
        rw [←primeRank_congr p e]
        exact hsq.stronglyQuasithin p hp (hp.odd_of_ne_two hp2)
      have hr1 := ChapterA.Section02.psu3_fieldExponent_eq_one J hp2
        (hpr ▸ hcard) hr (hpr ▸ hconj) hbound
      have hpq : p = q := by simpa [hr1] using hpr
      have hp3 := ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.source_unitaryRestriction
        ρ (⊤ : Subgroup H) ⟨hsq,hfit.symm,inferInstance,hf,hiTop⟩ hp
        (hp.odd_of_ne_two hp2) (hpq ▸ hmTop) hs.smallCubic
      omega

/-- A faithful binary FF action of a centerless SQTK quasisimple group excludes
both signed projective cubic families at their diagonal congruence. -/
theorem no_signed_projective_ff
    {H X : Type*} [Group H] [Finite H] [IsQuasisimple H]
    [AddCommGroup X] [Module (ZMod 2) X] [Module.Finite (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X) (hsq : IsSQTK KnownSimple.IsKnownSimple H)
    (hz : center H = ⊥) (hf : Function.Injective ρ) (hff : IsFFModule ρ)
    (u : Bool) (q : ℕ) (hq : SignedCongruence u q) (hm : IsPSLSign H u 3 q) : False := by
  obtain ⟨U,N,hi,hfaith,hffN⟩ := faithful_irreducible_ff_section ρ hz hf hff
  exact no_signed_projective_irreducible_ff N.quotientRepresentation hsq hz hfaith hi hffN u q hq hm

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : OutsideChoice T L} {K0 : Subgroup c.H} {n : ℕ} (m : OutsideSymplecticMarking c K0 n)

/-- Exclude the actual projective cubic actor, using its original faithful action
and the whole marked module offender. -/
theorem not_high_three_rank (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (hd : 3 ∣ 2 ^ n - 1) : ¬ 1 < primeRank 3 KZ := by
  intro hhigh
  let := hr.elementary
  let σ := (representation m hr).comp (image m KZ).subtype
  have hKN := hK.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨hz,_,u,q,hq,hm⟩ := secondary_image_projective_of_high_three_rank m hn h hr hUN hcore
    KZ hK hJK hcomp hquasi hnormal hd hhigh
  let := secondary_image_quasisimple m hn hr hUN hcore KZ hKN hJK hquasi hnormal
  have hsq := secondary_image_sqtk m hn h hr hUN hcore KZ hKN hJK hquasi hnormal
  have hBK := image_mono m ((m.fullModule_le_second hn).trans hJK)
  have hff : IsFFModule σ := ⟨(image m c.ordinaryModule).subgroupOf (image m KZ),
    ((fullModule_isBestOffender m hn hr hUN hcore hQ).subgroupOf
      (representation m hr) hBK).isOffender _⟩
  have hf : Function.Injective σ :=
    (representation_injective m hr).comp (image m KZ).subtype_injective
  exact no_signed_projective_ff σ hsq hz hf hff u q hq hm


/-- All Cartan primes have rank one in the original secondary component.
The cubic diagonal exception is now discharged, with no classification callback. -/
theorem secondary_primeRank_eq_one (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) :
    primeRank p KZ = 1 := by
  by_cases hp3 : p = 3
  · subst p
    exact le_antisymm (Nat.le_of_not_gt
      (not_high_three_rank m hn h hr hUN hcore hQ KZ hK hJK hcomp hquasi hnormal hd))
      (one_le_secondary_primeRank m hn KZ hJK 3 hp hd)
  · exact primeRank_eq_one_of_ne_three m hn h KZ hK hJK hcomp hquasi hnormal p hp ho hd hp3

/-- The same Cartan bound on the actual action image. Odd-prime cyclic Sylows
justify passage through the original action projection. -/
theorem secondary_image_primeRank_le_one (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2 ^ n - 1) :
    primeRank p (image m KZ) ≤ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let P : Sylow p KZ := Classical.choice inferInstance
  have hb := (secondary_primeRank_eq_one m hn h hr hUN hcore hQ KZ hK hJK hcomp
    hquasi hnormal p hp ho hd).le
  have hKN := hK.trans (Subgroup.centralizer_le_normalizer _)
  exact P.primeRank_le_one_of_surjective (P.isCyclic_of_odd_of_primeRank_le_one ho hb)
    (secondaryProjection m KZ hKN) (secondaryProjection_surjective m KZ hKN)

/-- Even degree now gives equality of the two actual embedded action images
without an additional cubic-rank premise. -/
theorem image_eq_of_even (hn : 1 < n) (he : Even n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G)) (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G)) :
    image m KZ = image m m.second := by
  apply image_eq_of_even_threeRank m hn he h hr hUN hcore hQ KZ
    (hK.trans (Subgroup.centralizer_le_normalizer _)) hJK hquasi hnormal
  exact secondary_image_primeRank_le_one m hn h hr hUN hcore hQ KZ hK hJK hcomp hquasi hnormal
    3 Nat.prime_three (by decide) ((Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr he)

/-- The even-degree branch establishes both literal terminal conclusions. -/
theorem module_and_containment_of_even (hn : 1 < n) (he : Even n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hseed : conjugateSpanBy c.ordinaryModule m.second = m.second)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hKZ : conjugateSpanBy m.second KZ = KZ)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G)) :
    m.rootSpan = m.second.pCoreIn 2 ∧ KZ ≤ m.second ⊔ m.rootCore := by
  exact module_and_containment_of_image_eq m hn hr hUN hcore hseed hQ KZ
    (hK.trans (Subgroup.centralizer_le_normalizer _)) hKZ hquasi hnormal
    (image_eq_of_even m hn he h hr hUN hcore hQ KZ hK
      ((le_conjugateSpanBy _ _).trans_eq hKZ) hcomp hquasi hnormal)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideRootFF
end


/-!
# The remaining odd-degree ordinary-root action rows

The original point local is a perfect extension with quotient SL₂(2ⁿ).
Every faithful binary representation of the secondary action image therefore
has dimension at least 2n. This excludes SL₄(2), SL₅(2), and their action
variants when n is odd. The literal inclusions A_d → A₈ ≃ SL₄(2) exclude
the alternating rows. Order divisibility removes the small symplectic and
triple-cover rows. The marked binary G₂ endpoint would identify its proper
derived subgroup with the full actor, contradicting its checked index two.

The complete source table thus leaves the natural SL₂ row and four larger
action rows, with their original moved-section equivalences. The natural
SL₂ comparison and the completed even-degree contradiction are applied to
the literal root consumer, leaving odd degree with natural or doubled SL₃,
nonbinary Sp₄, or nonbinary G₂. The remaining field and embedded-module
comparisons are still required for the full ordinary-root contradiction.

Source: Aschbacher–Smith 4.3.6, printed p.615; B.4.2 and B.5.1,
pp.86 and 99–103. The binary degree bound uses the actual SL₂
highest-weight and Frobenius-descent theorems through E.2.13(4), p.225.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideRootFF
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : OutsideChoice T L} {K0 : Subgroup c.H} {n : ℕ} (m : OutsideSymplecticMarking c K0 n)

/-- A faithful binary representation of the actual secondary image contains
a nontrivial section of the original perfect point local. Its marked SL₂
quotient forces dimension at least twice the original field degree. -/
theorem secondary_faithful_binary_degree (hn : 1 < n)
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hJK : m.second ≤ KZ)
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [Module.Finite (ZMod 2) X]
    (ρ : Representation (ZMod 2) (image m KZ) X) (hf : Function.Injective ρ) :
    2 * n ≤ Module.finrank (ZMod 2) X := by
  let d := secondNaturalExtension m hn
  have hF : 2 < Nat.card m.Field := by
    rw [m.card]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hn
  let := d.perfect hF
  let q := secondaryProjection m m.second m.second_le_rootNormalizer
  let f := (inclusion (image_mono m hJK)).comp q
  let σ := ρ.comp f
  have hnt : ∃ j, σ j ≠ 1 := by
    by_contra! ht
    have he : image m m.second = ⊥ := by
      apply bot_unique
      intro x hx
      obtain ⟨j,hj⟩ := secondaryProjection_surjective m m.second m.second_le_rootNormalizer ⟨x,hx⟩
      have hx1 : (inclusion (image_mono m hJK)) (q j) = 1 :=
        hf ((ht j).trans ρ.map_one.symm)
      exact (congrArg Subtype.val hj).symm.trans (congrArg Subtype.val hx1)
    exact second_image_ne_bot m hn hUN hcore he
  let e := QuotientGroup.liftEquiv (pCore 2 m.second) d.surjective d.kernel.symm
  exact SL2.perfect_core_quotient_finrank_bound e σ hnt (by omega) m.card

private theorem binary_embedding_bound (hn : 1 < n)
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hJK : m.second ≤ KZ)
    {d : ℕ} (f : image m KZ →* SL(d,ZMod 2)) (hf : Function.Injective f) :
    2 * n ≤ d := by
  simpa only [Module.finrank_fin_fun] using secondary_faithful_binary_degree m hn hUN hcore KZ hJK
    ((specialLinearNatural (k := ZMod 2) d).comp f)
    ((specialLinearNatural_injective d).comp hf)

private def altEightEmbedding {d : ℕ} (hd : d ≤ 8) :
    alternatingGroup (Fin d) →* alternatingGroup (Fin 8) :=
  (((Equiv.Perm.extendDomainHom (Fin.castLEEmb hd).toEquivRange).comp
    (alternatingGroup (Fin d)).subtype)).codRestrict _ (by
      intro x
      change Equiv.Perm.sign (x.val.extendDomain _) = 1
      rw [Equiv.Perm.sign_extendDomain]
      exact x.prop)

private theorem altEightEmbedding_injective {d : ℕ} (hd : d ≤ 8) :
    Function.Injective (altEightEmbedding hd) := by
  intro x y h
  apply Subtype.ext
  exact Equiv.Perm.extendDomainHom_injective (Fin.castLEEmb hd).toEquivRange (congrArg Subtype.val h)

private theorem no_small_alternating (hn : 1 < n) (ho : Odd n)
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hJK : m.second ≤ KZ)
    {d : ℕ} (hd : d ≤ 8) (e : image m KZ ≃* alternatingGroup (Fin d)) : False := by
  let a := Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans Atlas.Order20160A8.sl4TwoEquivPSL.symm
  let f := a.toMonoidHom.comp ((altEightEmbedding hd).comp e.toMonoidHom)
  have hb := binary_embedding_bound m hn hUN hcore KZ hJK f
    (a.injective.comp ((altEightEmbedding_injective hd).comp e.injective))
  have hodd := Nat.odd_iff.mp ho
  omega

omit [Finite G] in
private theorem image_order_dvd (hn : 1 < n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hJK : m.second ≤ KZ) :
    2^n*((2^n)^2-1) ∣ Nat.card (image m KZ) := by
  have hi := card_dvd_of_le (image_mono m hJK)
  rw [Nat.card_congr (secondImageEquiv m hn hr hUN hcore).toEquiv,
    BenderSuzuki.External.huppert614_card_specialLinearGroup,m.card] at hi
  exact hi

omit [Finite G] in
private theorem no_small_order (hn : 1 < n) (ho : Odd n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hJK : m.second ≤ KZ)
    (hc : Nat.card (image m KZ) ∣ 720 ∨ Nat.card (image m KZ) ∣ 1080) : False := by
  have hd := image_order_dvd m hn hr hUN hcore KZ hJK
  have ho' := Nat.odd_iff.mp ho
  rcases hc with hc | hc
  · have hd := hd.trans hc
    have hb : n < 5 := by
      by_contra! hb
      have hh := (Nat.pow_dvd_pow 2 hb).trans ((dvd_mul_right _ _).trans hd)
      norm_num at hh
    have hn3 : n = 3 := by omega
    norm_num [hn3] at hd
  · have hd := hd.trans hc
    have hb : n < 4 := by
      by_contra! hb
      have hh := (Nat.pow_dvd_pow 2 hb).trans ((dvd_mul_right _ _).trans hd)
      norm_num at hh
    have hn3 : n = 3 := by omega
    norm_num [hn3] at hd

private theorem marked_full_model_eq_top
    {H X E Y : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    [Group E] [AddCommGroup Y] [Module (ZMod 2) Y]
    {ρ : Representation (ZMod 2) H X} {σ : Representation (ZMod 2) E Y}
    {A : Subgroup H} {M : Subgroup E}
    (e : MarkedActionEquiv ρ A ⊤ σ M) : M = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨a,rfl⟩ := e.action.groupEquiv.surjective g
  have he := e.compatible (⟨a,mem_top _⟩ : (⊤ : Subgroup H))
  have hh : (⟨(a : H),e.contained (mem_top _)⟩ : A) = a := rfl
  rw [hh] at he
  exact he.symm ▸ (e.subgroupEquiv (⟨a,mem_top _⟩ : (⊤ : Subgroup H))).property

/-- The larger rows remaining after the finite exceptions are excluded. Every
alternative retains its action equivalence on the original moved section. -/
def OddHigherRows {H X : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X) (s : MovedSection ρ ⊤) : Prop :=
  (∃ (F : BinaryField), Nonempty
    (ActionEquiv (s.action.comp (⊤ : Subgroup H).subtype) (linearNatural F 3))) ∨
  (∃ (F : BinaryField), Nonempty
    (ActionEquiv (s.space.toRepresentation.comp (⊤ : Subgroup H).subtype)
      (repeated (linearNatural F 3) 2))) ∨
  (∃ (F : BinaryField), 1 < F.degree ∧ Nonempty
    (ActionEquiv (s.action.comp (⊤ : Subgroup H).subtype) (binarySymplectic F))) ∨
  (∃ (F : BinaryField), 1 < F.degree ∧ Nonempty
    (ActionEquiv (s.action.comp (⊤ : Subgroup H).subtype) (binaryG2 F)))

/-- The retained rows expose their literal action comparisons to subsequent consumers. -/
theorem oddHigherRows_iff {H X : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X) (s : MovedSection ρ ⊤) :
    OddHigherRows ρ s ↔
      (∃ (F : BinaryField), Nonempty
        (ActionEquiv (s.action.comp (⊤ : Subgroup H).subtype) (linearNatural F 3))) ∨
      (∃ (F : BinaryField), Nonempty
        (ActionEquiv (s.space.toRepresentation.comp (⊤ : Subgroup H).subtype)
          (repeated (linearNatural F 3) 2))) ∨
      (∃ (F : BinaryField), 1 < F.degree ∧ Nonempty
        (ActionEquiv (s.action.comp (⊤ : Subgroup H).subtype) (binarySymplectic F))) ∨
      (∃ (F : BinaryField), 1 < F.degree ∧ Nonempty
        (ActionEquiv (s.action.comp (⊤ : Subgroup H).subtype) (binaryG2 F))) := Iff.rfl

/-- The natural rank-one row, or one of the retained larger action rows. -/
def OddRows {H X : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X) (s : MovedSection ρ ⊤) : Prop :=
  (∃ (F : BinaryField)
      (_e : ActionEquiv (s.action.comp (⊤ : Subgroup H).subtype) (linearNatural F 2)),
      ∀ A, IsBestOffender s.action A → ∃ S : Sylow 2 (⊤ : Subgroup H),
        A = (S : Subgroup (⊤ : Subgroup H)).map (⊤ : Subgroup H).subtype) ∨
  OddHigherRows ρ s

/-- The full B.5.1/B.4.2 table excludes all finite exceptional actors at odd
source degree, using the original embedded point image. -/
theorem oddRows_of_source (hn : 1 < n) (ho : Odd n)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hJK : m.second ≤ KZ)
    (s : letI := hr.elementary
      ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((representation m hr).comp (image m KZ).subtype) ⊤) :
    letI := hr.elementary
    OddRows ((representation m hr).comp (image m KZ).subtype) s.sectionData := by
  let := hr.elementary
  have noLin {d : ℕ} (hd : d = 4 ∨ d = 5)
      (e : (⊤ : Subgroup (image m KZ)) ≃* SL(d,ZMod 2)) : False := by
    have hb := binary_embedding_bound m hn hUN hcore KZ hJK
      (topEquiv.symm.trans e).toMonoidHom (topEquiv.symm.trans e).injective
    have hh := Nat.odd_iff.mp ho
    omega
  have noAlt {d : ℕ} (hd : d ≤ 8)
      (e : (⊤ : Subgroup (image m KZ)) ≃* alternatingGroup (Fin d)) : False :=
    no_small_alternating m hn ho hUN hcore KZ hJK hd (topEquiv.symm.trans e)
  cases s.clause_one with
  | doubleThree F _ e _ _ => exact Or.inr (Or.inr (Or.inl ⟨F,⟨e⟩⟩))
  | naturalDual d hd _ e => exact (noLin hd e.some.groupEquiv).elim
  | repeatedNatural d r hd _ _ _ e => exact (noLin hd e.some.groupEquiv).elim
  | irreducible _ hf _ hs _ =>
    cases hs with
    | linearTwo F _ e ha _ => exact Or.inl ⟨F,e,ha⟩
    | linearThree F _ e _ => exact Or.inr (Or.inl ⟨F,⟨e⟩⟩)
    | symplectic F hF _ e _ => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨F,hF,⟨e⟩⟩)))
    | g2 F hF _ e _ _ => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨F,hF,⟨e⟩⟩)))
    | g2Two e _ _ =>
      have he := marked_full_model_eq_top e
      have hi : (commutator (Atlas.G2.Model (ZMod 2))).index = 2 := by
        rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
          Atlas.G2.BinaryException.index_H]
      rw [he,index_top] at hi
      contradiction
    | symmetric d hd e _ _ => exact (noAlt (by omega) e.subgroupEquiv).elim
    | alternatingSix _ e _ _ => exact (noAlt (by decide) e.groupEquiv).elim
    | alternatingSeven _ _ e _ _ _ => exact (noAlt (by decide) e).elim
    | orthogonalSix _ _ e _ _ => exact (noAlt (by decide) e.groupEquiv).elim
    | symmetricEight _ e _ => exact (noAlt (by decide) e.subgroupEquiv).elim
    | binaryLinear d hd _ e _ => exact (noLin hd e.groupEquiv).elim
    | exteriorFive _ _ e _ _ _ => exact (noLin (Or.inr rfl) e).elim
    | symplecticTwo e _ =>
      apply False.elim
      apply no_small_order m hn ho hr hUN hcore KZ hJK
      left
      rw [Nat.card_congr (topEquiv.symm.trans e.subgroupEquiv).toEquiv]
      exact (Subgroup.card_subgroup_dvd_card (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))).trans
        (by rw [Theory.SpecificGroups.SymplecticFour.Binary.card_sp_two])
    | tripleSix _ a _ =>
      apply False.elim
      apply no_small_order m hn ho hr hUN hcore KZ hJK
      right
      rw [← Nat.card_congr (topEquiv : (⊤ : Subgroup (image m KZ)) ≃* image m KZ).toEquiv,
        Subgroup.card_eq_card_quotient_mul_card_subgroup (center (⊤ : Subgroup (image m KZ))),
        Nat.card_congr a.centerEquiv.toEquiv,Nat.card_congr a.quotientEquiv.toEquiv,
        nat_card_alternatingGroup]
      norm_num

/-- Apply the complete classification to the actual secondary action. The
rank-one row gives equality inside the original actor; the remaining rows
retain their moved-section coordinates for the field comparison. -/
theorem image_eq_or_oddHigherRows (hn : 1 < n) (ho : Odd n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hKN : KZ ≤ m.rootNormalizer) (hJK : m.second ≤ KZ)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G)) :
    letI := hr.elementary
    image m KZ = image m m.second ∨
      ∃ s : MovedSection ((representation m hr).comp (image m KZ).subtype) ⊤,
        OddHigherRows ((representation m hr).comp (image m KZ).subtype) s := by
  let := hr.elementary
  obtain ⟨s⟩ := secondary_source_classification m hn h hr hUN hcore hQ KZ hKN hJK hquasi hnormal
  rcases oddRows_of_source m hn ho hr hUN hcore KZ hJK s with ⟨F,e,ha⟩ | hs
  · exact Or.inl (image_eq_of_linearTwo_section m hn hr hUN hcore hQ KZ hJK s.sectionData F e ha)
  · exact Or.inr ⟨s.sectionData,hs⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideRootFF
end


/-!
# Completing the odd-degree ordinary-root action comparison

Retain the original W-image inside the embedded J-image, identified with
SL₂(2ⁿ) by its actual action projection. The offender descends to the literal
moved section in each remaining B.5.1/B.4.2 row. The involution displacement
bound and the Sylow order force its fixed codimension to be n. Thus the
model field degree divides n, by restriction of scalars.

Every nonbinary model has a rank-two split torus at some prime dividing
its multiplicative field order. This prime also divides 2ⁿ−1, contradicting
the proved rank-one restriction on the original secondary action image.
The possible binary SL₃ endpoint is excluded by the faithful binary degree
bound for the embedded point local. This handles the natural and doubled
SL₃ rows and the nonbinary symplectic and G₂ rows with their actual actions.
Together with the completed even-degree and rank-one comparisons, this gives
equality of the two subgroups inside the original centralizer quotient.

Source: Aschbacher–Smith 4.3.6, printed p.615; B.4.2 and B.5.1,
pp.86 and 99–103; E.2.13(4), p.225.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideRootFF
open ChapterB.QuasisimpleSource

private theorem binaryField_finrank (F : BinaryField) :
    Module.finrank (ZMod 2) F.Carrier = F.degree := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)
  rw [Nat.card_zmod,F.card_eq] at h
  exact (Nat.pow_right_injective (by decide : 1 < 2) h).symm

private theorem restrict_injective
    {F H X : Type*} [Field F] [Algebra (ZMod 2) F] [Group H]
    [AddCommGroup X] [Module F X] [Module (ZMod 2) X] [IsScalarTower (ZMod 2) F X]
    (ρ : Representation F H X) (hf : Function.Injective ρ) :
    Function.Injective (restrictScalars (k := ZMod 2) ρ) := by
  intro a b h
  apply hf
  ext x
  exact LinearMap.congr_fun h x

private def removeTop
    {H E X Y : Type*} [Group H] [Group E] [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    {ρ : Representation (ZMod 2) H X} {σ : Representation (ZMod 2) E Y}
    (e : ActionEquiv (ρ.comp (⊤ : Subgroup H).subtype) σ) : ActionEquiv ρ σ :=
  ⟨topEquiv.symm.trans e.groupEquiv,e.linearEquiv,fun g v => e.intertwines (topEquiv.symm g) v⟩

private theorem model_fieldDegree_dvd
    {H E X Y K : Type*} [Group H] [Finite H] [Group E] [Finite E]
    [AddCommGroup X] [Module (ZMod 2) X]
    [Field K] [Finite K] [CharP K 2]
    (F : BinaryField) [AddCommGroup Y] [Module F.Carrier Y]
    [Module (ZMod 2) Y] [IsScalarTower (ZMod 2) F.Carrier Y]
    [Module.Finite (ZMod 2) Y]
    {ρ : Representation (ZMod 2) H X} (τ : Representation F.Carrier E Y)
    (hf : Function.Injective τ)
    (J A : Subgroup H) (hAJ : A ≤ J) (eJ : J ≃* SL(2,K))
    {n : ℕ} (hn : 1 < n) (hK : Nat.card K = 2^n)
    (hA : IsOffender ρ A)
    (e : ActionEquiv (ρ.comp (⊤ : Subgroup H).subtype) (restrictScalars (k := ZMod 2) τ)) :
    F.degree ∣ n := by
  let a := removeTop e
  let f := a.groupEquiv.toMonoidHom
  let J' := J.map f
  let A' := A.map f
  have hA' := hA.map_equivariant ρ (restrictScalars (k := ZMod 2) τ)
    f a.groupEquiv.injective a.linearEquiv a.intertwines
  let eJ' : J' ≃* SL(2,K) :=
    (J.equivMapOfInjective f a.groupEquiv.injective).symm.trans eJ
  have hd := SL2.scalar_degree_dvd_of_offender τ (restrict_injective τ hf)
    J' A' (map_mono hAJ) eJ' hn hK hA'
  rwa [binaryField_finrank] at hd

private def scalarDouble {F H X : Type*} [Field F] [Group H]
    [AddCommGroup X] [Module F X] (ρ : Representation F H X) :
    Representation F H (Fin 2 → X) where
  toFun g := {
    toFun := fun v i => ρ g (v i)
    map_add' := by intros; ext; simp
    map_smul' := by intros; ext; simp }
  map_one' := by
    apply LinearMap.ext
    intro v
    funext i
    exact LinearMap.congr_fun ρ.map_one (v i)
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    funext i
    exact LinearMap.congr_fun (ρ.map_mul g h) (v i)

private theorem scalarDouble_injective {F H X : Type*} [Field F] [Group H]
    [AddCommGroup X] [Module F X] (ρ : Representation F H X)
    (hf : Function.Injective ρ) : Function.Injective (scalarDouble ρ) := by
  intro a b he
  apply hf
  ext x
  exact congrFun (LinearMap.congr_fun he (fun _ => x)) 0

private theorem symplectic_faithful (F : BinaryField) :
    Function.Injective (symplecticNatural (k := F.Carrier) 2) := by
  intro a b h
  apply Subtype.ext
  exact Matrix.toLin'.injective h

private theorem g2_split_rank (F : BinaryField) (p : ℕ) [Fact p.Prime]
    (hd : p ∣ Nat.card F.Carrier - 1) : 2 ≤ primeRank p (Atlas.G2.Model F.Carrier) := by
  have hu : 1 ≤ primeRank p F.Carrierˣ := by
    by_contra hh
    have hz : primeRank p F.Carrierˣ = 0 := by omega
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp hz (by simpa only [Nat.card_units] using hd)
  have hi := Theory.GroupTheory.primeRank_le_of_injective p
    (Atlas.G2.torusHom (K := F.Carrier)) Atlas.G2.torusHom_injective
  rw [primeRank_prod_eq_add] at hi
  omega

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : OutsideChoice T L} {K0 : Subgroup c.H} {n : ℕ} (m : OutsideSymplecticMarking c K0 n)

private theorem linearThree_degree_gt_one (hn : 1 < n)
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (KZ : Subgroup G) (hJK : m.second ≤ KZ)
    (F : BinaryField) (e : (⊤ : Subgroup (image m KZ)) ≃* SL(3,F.Carrier)) :
    1 < F.degree := by
  let a := topEquiv.symm.trans e
  let ρ := (linearNatural F 3).comp a.toMonoidHom
  have hf := (restrict_injective (specialLinearNatural (k := F.Carrier) 3)
    (specialLinearNatural_injective 3)).comp a.injective
  have hb := secondary_faithful_binary_degree m hn hUN hcore KZ hJK ρ hf
  have hd : Module.finrank (ZMod 2) (Fin 3 → F.Carrier) = 3 * F.degree := by
    rw [←Module.finrank_mul_finrank (ZMod 2) F.Carrier,
      Module.finrank_fin_fun,binaryField_finrank,mul_comm]
  rw [hd] at hb
  omega

private theorem incompatible_field_degree
    (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G)) (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (F : BinaryField) (hF : 1 < F.degree) (hd : F.degree ∣ n)
    {E : Type*} [Group E] [Finite E] (e : (⊤ : Subgroup (image m KZ)) ≃* E)
    (hlower : ∀ p, p.Prime → p ∣ Nat.card F.Carrier - 1 → 2 ≤ primeRank p E) : False := by
  have hpow : 2 < 2^F.degree :=
    Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hF
  obtain ⟨p,hp,hpdiv⟩ := Nat.exists_prime_and_dvd (by omega : 2^F.degree - 1 ≠ 1)
  have hpn : p ∣ 2^n-1 := hpdiv.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hd)
  have hpodd : Odd p := hp.odd_of_ne_two (by
    intro he
    subst p
    have heven := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega : F.degree ≠ 0))
    have hodd := Nat.mod_eq_zero_of_dvd hpdiv
    omega)
  have hb := secondary_image_primeRank_le_one m hn h hr hUN hcore hQ KZ hK hJK
    hcomp hquasi hnormal p hp hpodd hpn
  have hl := hlower p hp (F.card_eq.symm ▸ hpdiv)
  rw [primeRank_congr p (topEquiv.symm.trans e)] at hb
  omega

/-- Exclude all four retained higher rows using the original embedded offender
and the already proved Cartan-prime restriction; no model premise remains. -/
theorem not_oddHigherRows (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G)) (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G))
    (s : letI := hr.elementary
      MovedSection ((representation m hr).comp (image m KZ).subtype) ⊤) :
    letI := hr.elementary
    ¬ OddHigherRows ((representation m hr).comp (image m KZ).subtype) s := by
  let := hr.elementary
  let H := image m KZ
  let J := (image m m.second).subgroupOf H
  let A := (image m c.ordinaryModule).subgroupOf H
  have hJH := image_mono m hJK
  have hWH := image_mono m ((m.fullModule_le_second hn).trans hJK)
  have hAJ : A ≤ J := fun _ hx => image_mono m (m.fullModule_le_second hn) hx
  let eJ : J ≃* SL(2,m.Field) :=
    (subgroupOfEquivOfLe hJH).trans (secondImageEquiv m hn hr hUN hcore)
  have hA : IsOffender ((representation m hr).comp H.subtype) A :=
    (fullModule_isOffender m hn hr hUN hcore hQ).subgroupOf (representation m hr) hWH
  have hAm : IsOffender s.space.toRepresentation A :=
    ⟨hA.1,(fixedCodim_subrepresentation_le _ s.space A).trans hA.2⟩
  have hAs : IsOffender s.action A := by
    refine ⟨hA.1,?_⟩
    have hq := fixedCodim_quotient_add_subrepresentation_le s.space.toRepresentation s.central A
    have ha := hAm.2
    change fixedCodim s.action A + _ ≤ _ at hq
    omega
  rw [oddHigherRows_iff]
  rintro (⟨F,⟨e⟩⟩ | ⟨F,⟨e⟩⟩ | ⟨F,hF,⟨e⟩⟩ | ⟨F,hF,⟨e⟩⟩)
  · have hd := model_fieldDegree_dvd F (specialLinearNatural 3)
      (specialLinearNatural_injective 3) J A hAJ eJ hn m.card hAs e
    apply incompatible_field_degree m hn h hr hUN hcore hQ KZ hK hJK hcomp hquasi hnormal
      F (linearThree_degree_gt_one m hn hUN hcore KZ hJK F e.groupEquiv) hd e.groupEquiv
    intro p hp hd
    let : Fact p.Prime := ⟨hp⟩
    exact Matrix.PSL3.SplitPrimeRank.special_rank F.Carrier hd
  · let τ := scalarDouble (specialLinearNatural (k := F.Carrier) 3)
    have he : ActionEquiv (s.space.toRepresentation.comp (⊤ : Subgroup H).subtype)
        (restrictScalars (k := ZMod 2) τ) := e
    have hd := model_fieldDegree_dvd F τ
      (scalarDouble_injective _ (specialLinearNatural_injective 3)) J A hAJ eJ hn m.card hAm he
    apply incompatible_field_degree m hn h hr hUN hcore hQ KZ hK hJK hcomp hquasi hnormal
      F (linearThree_degree_gt_one m hn hUN hcore KZ hJK F e.groupEquiv) hd e.groupEquiv
    intro p hp hd
    let : Fact p.Prime := ⟨hp⟩
    exact Matrix.PSL3.SplitPrimeRank.special_rank F.Carrier hd
  · have hd := model_fieldDegree_dvd F (symplecticNatural 2)
      (symplectic_faithful F) J A hAJ eJ hn m.card hAs e
    apply incompatible_field_degree m hn h hr hUN hcore hQ KZ hK hJK hcomp hquasi hnormal F hF hd e.groupEquiv
    exact fun p hp hd => Theory.SpecificGroups.SymplecticFour.split_torus_prime_rank hp hd
  · have hd := model_fieldDegree_dvd F (g2Natural F.Carrier)
      (Atlas.G2.Natural.action_injective F.Carrier) J A hAJ eJ hn m.card hAs e
    apply incompatible_field_degree m hn h hr hUN hcore hQ KZ hK hJK hcomp hquasi hnormal F hF hd e.groupEquiv
    intro p hp hd
    let : Fact p.Prime := ⟨hp⟩
    exact g2_split_rank F p hd

/-- The full source table gives equality of the two subgroups inside the
original centralizer quotient, in every source field degree. -/
theorem secondary_image_eq_second (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G)) (hJK : m.second ≤ KZ)
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G)) :
    image m KZ = image m m.second := by
  rcases Nat.even_or_odd n with he | ho
  · exact image_eq_of_even m hn he h hr hUN hcore hQ KZ hK hJK hcomp hquasi hnormal
  · let := hr.elementary
    rcases image_eq_or_oddHigherRows m hn ho h hr hUN hcore hQ KZ
      (hK.trans (Subgroup.centralizer_le_normalizer _)) hJK hquasi hnormal with he | ⟨s,hs⟩
    · exact he
    · exact (not_oddHigherRows m hn h hr hUN hcore hQ KZ hK hJK hcomp hquasi hnormal s hs).elim

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideRootFF
end


/-!
# The conditional ordinary-root failure-of-factorization contradiction

The complete action comparison identifies the secondary and point-local
images inside the original centralizer quotient. The exact action-kernel
calculation then gives U = O₂(J) and K_Z ≤ JQ. Applying these two proved
conclusions to the original root geometry gives the source contradiction.

The raw-choice root-core and secondary inputs remain explicit here and
are discharged by SourceSelectionOrdinaryComplete. There is no classification,
model-selection or prime-rank parameter.

Source: Aschbacher–Smith 4.3.6, printed p.615, the last two paragraphs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideRootFF
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : OutsideChoice T L} {K0 : Subgroup c.H} {n : ℕ} (m : OutsideSymplecticMarking c K0 n)

/-- Both terminal subgroup conclusions, with the original quotient kernel and root marking. -/
theorem module_and_containment (hn : 1 < n)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : IsPReduced 2 (moduleSubgroup m))
    (hUN : m.rootSpan ≤ m.rootNormalizer) (hcore : m.second.pCoreIn 2 ≤ m.rootSpan)
    (hseed : conjugateSpanBy c.ordinaryModule m.second = m.second)
    (hQ : m.rootCore = m.second.pCoreIn 2 ⊔
      (m.rootCore ⊓ centralizer (c.ordinaryModule : Set G)))
    (KZ : Subgroup G) (hK : KZ ≤ centralizer (m.root : Set G))
    (hcomp : (KZ.subgroupOf (centralizer (m.root : Set G))).IsCComponent)
    (hKZ : conjugateSpanBy m.second KZ = KZ)
    (hquasi : IsQuasisimple (KZ ⧸ pCore 2 KZ))
    (hnormal : m.rootNormalizer ≤ normalizer (KZ : Set G)) :
    m.rootSpan = m.second.pCoreIn 2 ∧ KZ ≤ m.second ⊔ m.rootCore := by
  apply module_and_containment_of_image_eq m hn hr hUN hcore hseed hQ KZ
    (hK.trans (Subgroup.centralizer_le_normalizer _)) hKZ hquasi hnormal
  exact secondary_image_eq_second m hn h hr hUN hcore hQ KZ hK
    ((le_conjugateSpanBy _ _).trans_eq hKZ) hcomp hquasi hnormal

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideRootFF
end
