module

public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.AlternatingEndpoints
public import GorensteinWalter.PSL2FourUniversalCover
public import GorensteinWalter.SL2UniversalCover
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.G2.MultiplierOrdinary
public import Theory.SpecificGroups.G2.MultiplierFourTwoGroup
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.Source
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers
public import Theory.SpecificGroups.Suzuki.SchurCoverReduction
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.SU3.TernaryPerfectCover
public import Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimary.PresentationFaithfulness
public import Theory.SpecificGroups.LinearHigher.OddKernelLifts
public import Theory.SpecificGroups.PSL5Two.UniversalCover
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound
public import Theory.SpecificGroups.SymplecticSix.EvenProjective
public import Theory.SpecificGroups.SymplecticSix.FieldTransport
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient

/-!
# Further low-rank Case II cover exclusions in A.2.18

The selected odd prime divides the nontrivial center of the original source
counterexample. Actual central-cover calculations exclude it for binary PSL2,
PSp4 and G2. The exceptional G2(4) calculation needs only a two-group kernel.
The complete Parrott presentation calculation removes the center in the Tits
case. Every projection is the given quotient by the whole original center.

Source: Aschbacher--Smith A.2.18, printed p.40, using the multiplier
calculations of I.1.3--4, printed pp.407--408.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] [IsQuasisimple G] {p : ℕ}

omit [IsQuasisimple G] in
private theorem selectedPrime_ne_two (h : CounterexampleToTheoremA K G S p) : p ≠ 2 := by
  intro hp
  have ho := h.2.2.2.2.2.1
  rw [hp] at ho
  exact (by decide : ¬ Odd (2 : ℕ)) ho

private theorem false_of_two_group_center
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (h2 : IsPGroup 2 (center G)) : False := by
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hd := h.prime_dvd_center ih
  rw [hk] at hd
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq h.2.2.2.2.1 Nat.prime_two).mp
    (h.2.2.2.2.1.dvd_of_dvd_pow hd)
  exact selectedPrime_ne_two h hp2

/-- The complete binary PSL2 central-quotient branch, including q=4. -/
theorem caseII_linear_two_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {a : ℕ} (ha : 2 ≤ a)
    (iso : ClassicalGroup.IsPSL (G ⧸ center G) 2 (2 ^ a)) : False := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := iso
  by_cases ha2 : a = 2
  · have hc4 : Nat.card F = 4 := by simpa [ha2] using hcard
    obtain ⟨ea⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hc4
    exact caseII_alternating_of_source h ih (by decide : 5 ≤ 5) (e.trans ea)
  have hlarge : 7 ≤ Nat.card F := by
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 3 ≤ a by omega)
    rw [hcard]
    omega
  let : Fact (3 < Nat.card F) := ⟨by omega⟩
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  let c := (centralQuotientCover e).toCovering
  have hc : Nat.Coprime p (Nat.card F) := by
    rw [hcard]
    exact ((Nat.coprime_primes h.2.2.2.2.1 Nat.prime_two).mpr
      (selectedPrime_ne_two h)).pow_right a
  have hn := GorensteinWalter.PSL2Cover.odd_prime_not_dvd_kernel F c hlarge p
    (selectedPrime_ne_two h) hc
  exact hn (by simpa [c, Cover.toCovering] using h.prime_dvd_center ih)

/-- The binary projective symplectic rank-two quotient has no odd-primary cover in Case II. -/
theorem caseII_symplectic_two_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {a : ℕ}
    (iso : ClassicalGroup.IsPSp (G ⧸ center G) 2 (2 ^ a)) : False := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := iso
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  let c := centralQuotientCover
    (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)
  have hn := Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary.not_dvd_card_kernel
    (selectedPrime_ne_two h) c.toMonoidHom c.surjective c.ker_le_center
  exact hn (by simpa [c] using h.prime_dvd_center ih)

/-- Every binary G2 model in its simple range is excluded in the original Case II. -/
theorem caseII_g2_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {a : ℕ} (ha : 2 ≤ a)
    (iso : ClassificationModels.IsG2At (G ⧸ center G) (2 ^ a)) : False := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := iso
  by_cases ha2 : a = 2
  · have hc4 : Nat.card F = 4 := by simpa [ha2] using hcard
    let : Fact (2 < Nat.card F) := ⟨by omega⟩
    have hker := Atlas.G2.FiniteCover.MultiplierFourBound.universalKernel_isPGroup_of_card_four hc4
    have hcent := (centralQuotientCover e).ker_isPGroup_of_universal
      (universalCover (Atlas.G2.Model F)) (universalCover_isUniversal (G := Atlas.G2.Model F)) hker
    rw [centralQuotientCover_ker] at hcent
    exact false_of_two_group_center h ih hcent
  · exact h.center_ne_bot ih (center_eq_bot_of_centralQuotientEquiv
      (Atlas.G2.MultiplierOrdinary.even_universalProjection_ker_eq_bot_of_card_pow
        hcard (by omega)) e)

/-- The complete literal Tits presentation calculation excludes its central quotient in Case II. -/
theorem caseII_tits
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (iso : Nonempty (G ⧸ center G ≃* Tits.ParrottGroup)) : False := by
  obtain ⟨e⟩ := iso
  exact h.center_ne_bot ih (center_eq_bot_of_centralQuotientEquiv
    Tits.CentralCoverLifting.CompatibleGenerators.universalProjection_ker_eq_bot e)


/-- The odd-center exclusion for every genuine binary triality parameter, including exponent one. -/
theorem caseII_triality_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {a : ℕ} (ha : 0 < a)
    (iso : Triality.Standard.IsTrialityGroupAt (2 ^ a) (G ⧸ center G)) : False :=
  false_of_two_group_center h ih
    (Triality.InnerDisplacement.PrimeToTwoCovers.center_isTwoGroup a ha iso)

/-- Cyclic odd Sylow transfer excludes all Suzuki central quotients in Case II. -/
theorem caseII_suzuki_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {m : ℕ} (hm : 0 < m)
    (iso : Nonempty (G ⧸ center G ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) : False := by
  obtain ⟨e⟩ := iso
  have hcent := BenderSuzuki.MatrixGroups.SchurCover.kernel_isTwoGroup hm
    (centralQuotientCover e)
  rw [centralQuotientCover_ker] at hcent
  exact false_of_two_group_center h ih hcent


/-- The literal small symplectic derived carrier is handled by the original alternating-cover exclusion. -/
theorem caseII_symplectic_derived_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (iso : Nonempty (G ⧸ center G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) : False := by
  obtain ⟨e⟩ := iso
  exact caseII_alternating_of_source h ih (by decide : 5 ≤ 6)
    (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)

/-- The actual binary G2 derived carrier has no odd-primary covering kernel. -/
theorem caseII_g2_derived_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (iso : Nonempty (G ⧸ center G ≃* commutator (Atlas.G2.Model (ZMod 2)))) : False := by
  obtain ⟨e⟩ := iso
  have hcent := BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover.binaryDerived_kernel_isTwoGroup
    (centralQuotientCover e)
  rw [centralQuotientCover_ker] at hcent
  exact false_of_two_group_center h ih hcent


/-- Odd root lifts and the proved SL4 presentation exclude every binary degree-four quotient. -/
theorem caseII_linear_four_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {a : ℕ} (ha : 0 < a)
    (iso : ClassicalGroup.IsPSL (G ⧸ center G) 4 (2 ^ a)) : False := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := iso
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  have ho := center_odd_of_source h ih
  let c := centralQuotientCover e
  obtain ⟨s, hs, _, hsc⟩ := Theory.SpecificGroups.LinearHigher.exists_covering_of_matrixMap_injective
    c.toMonoidHom c.surjective c.ker_le_center
    (by simpa [c] using Nat.coprime_two_right.mpr ho)
    (by decide : 2 ≤ 4)
    Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimaryFaithfulness.matrixMap_injective
  have hco : Odd (Nat.card F - 1) := by
    have hev : Even (2 ^ a : ℕ) := even_two.pow_of_ne_zero (by omega : a ≠ 0)
    have hpos : 0 < (2 : ℕ) ^ a := pow_pos (by decide) _
    rw [hcard]
    obtain ⟨m, hm⟩ := hev
    refine ⟨m - 1, ?_⟩
    omega
  have hc : Nat.card (center SL(4, F)) = 1 := by
    rw [Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
    exact (show Nat.Coprime 4 (Nat.card F - 1) from
      (Nat.coprime_two_left.mpr hco).pow_left 2).gcd_eq_one
  have hbot := (center SL(4, F)).eq_bot_of_card_eq hc
  have hsker : s.ker = ⊥ := le_bot_iff.mp (hbot ▸ hsc)
  let se : SL(4, F) ≃* G := MulEquiv.ofBijective s ⟨s.ker_eq_bot_iff.mp hsker, hs⟩
  exact h.center_ne_bot ih ((center G).eq_bot_of_card_eq
    ((Nat.card_congr (centerCongr se).toEquiv).symm.trans hc))

/-- The actual PSL5(2) universal-kernel calculation excludes this remaining binary linear quotient. -/
theorem caseII_binary_linear_five
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (iso : ClassicalGroup.IsPSL (G ⧸ center G) 5 2) : False := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := iso
  exact h.center_ne_bot ih (center_eq_bot_of_centralQuotientEquiv
    Theory.SpecificGroups.PSL5Two.UniversalCover.universalProjection_ker_eq_bot
    (e.trans (Theory.SpecificGroups.PSL5Two.UniversalCover.fieldEquiv F hcard)))

/-- The binary symplectic rank-three universal kernel is a two-group, so its odd cover is impossible. -/
theorem caseII_binary_symplectic_six_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (iso : ClassicalGroup.IsPSp (G ⧸ center G) 3 2) : False := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := iso
  let ep := (e.trans (Theory.SpecificGroups.SymplecticSix.pspFieldEquivZModTwo F hcard)).trans
    Theory.SpecificGroups.SymplecticSix.EvenProjective.equiv.symm
  have hk : IsPGroup 2 Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.projection.ker := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    have hlo := Nat.card_pos (α := Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.projection.ker)
    have hhi := Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.kernel_card_le_two
    have hcases : Nat.card Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.projection.ker = 1 ∨
        Nat.card Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.projection.ker = 2 := by omega
    change Nat.card Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.projection.ker ∣ 2
    rcases hcases with he | he
    · simpa only [he] using one_dvd 2
    · simpa only [he] using dvd_refl (2 : ℕ)
  have hcent := (centralQuotientCover ep).ker_isPGroup_of_universal
    (universalCover Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.Base)
    (universalCover_isUniversal (G := Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.Base)) hk
  rw [centralQuotientCover_ker] at hcent
  exact false_of_two_group_center h ih hcent

/-- Compatibility wrapper retaining the explicit prime-primary center. -/
theorem caseII_symplectic_two
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hP : IsPGroup p (center G)) {a : ℕ}
    (iso : ClassicalGroup.IsPSp (G ⧸ center G) 2 (2 ^ a)) : False := by
  have _primary := hP
  exact caseII_symplectic_two_of_source h ih iso

/-- Compatibility wrapper retaining the explicit prime-primary center. -/
theorem caseII_g2
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hP : IsPGroup p (center G)) {a : ℕ} (ha : 2 ≤ a)
    (iso : ClassificationModels.IsG2At (G ⧸ center G) (2 ^ a)) : False := by
  have _primary := hP
  exact caseII_g2_of_source h ih ha iso

/-- Compatibility wrapper retaining the explicit prime-primary center. -/
theorem caseII_triality
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hP : IsPGroup p (center G)) {a : ℕ} (ha : 0 < a)
    (iso : Triality.Standard.IsTrialityGroupAt (2 ^ a) (G ⧸ center G)) : False := by
  have _primary := hP
  exact caseII_triality_of_source h ih ha iso

/-- Compatibility wrapper retaining the explicit prime-primary center. -/
theorem caseII_suzuki
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hP : IsPGroup p (center G)) {m : ℕ} (hm : 0 < m)
    (iso : Nonempty (G ⧸ center G ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) : False := by
  have _primary := hP
  exact caseII_suzuki_of_source h ih hm iso

/-- Compatibility wrapper retaining the explicit prime-primary center. -/
theorem caseII_g2_derived
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hP : IsPGroup p (center G))
    (iso : Nonempty (G ⧸ center G ≃* commutator (Atlas.G2.Model (ZMod 2)))) : False := by
  have _primary := hP
  exact caseII_g2_derived_of_source h ih iso

/-- Compatibility wrapper retaining the explicit prime-primary center. -/
theorem caseII_linear_four
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hP : IsPGroup p (center G)) {a : ℕ} (ha : 0 < a)
    (iso : ClassicalGroup.IsPSL (G ⧸ center G) 4 (2 ^ a)) : False := by
  have _primary := hP
  exact caseII_linear_four_of_source h ih ha iso

/-- Compatibility wrapper retaining the explicit prime-primary center. -/
theorem caseII_binary_symplectic_six
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hP : IsPGroup p (center G))
    (iso : ClassicalGroup.IsPSp (G ⧸ center G) 3 2) : False := by
  have _primary := hP
  exact caseII_binary_symplectic_six_of_source h ih iso

/-- Compatibility wrapper retaining the explicit prime-primary center. -/
theorem caseII_linear_two
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hP : IsPGroup p (center G)) {a : ℕ} (ha : 2 ≤ a)
    (iso : ClassicalGroup.IsPSL (G ⧸ center G) 2 (2 ^ a)) : False := by
  have _primary := hP
  exact caseII_linear_two_of_source h ih ha iso

/-- Compatibility wrapper retaining the explicit prime-primary center. -/
theorem caseII_symplectic_derived
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hP : IsPGroup p (center G))
    (iso : Nonempty (G ⧸ center G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) : False := by
  have _primary := hP
  exact caseII_symplectic_derived_of_source h ih iso

end CFSG.Quasithin.ChapterA.Section02.EvenLie
