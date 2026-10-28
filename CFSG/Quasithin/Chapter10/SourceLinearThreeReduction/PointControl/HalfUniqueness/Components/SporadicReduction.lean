module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.OddThreeContaining
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.AlternatingContaining
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.QuadraticLinearContaining
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.TrialityContaining
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.ReeContaining
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.JankoContaining

/-!
# Reducing the strict containing component to a sporadic quotient

Odd-core removal makes the literal two-core quotient of a quasisimple
containing component simple. Its inherited SQTK structure gives the full
Theorem C catalogue. The checked containing-pair arguments exclude every
nonsporadic row, including odd ternary models and all eight rank-two cases.
The two applications retain the original ordered pair and exchanger; no
component-distinctness or cubic-divisor premise is added.

The sporadic exclusions, the zero-kernel binary-three normalizer and final
assembly remain with qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is
supplied by qt-d-10-nona5-point-selection; qt-d-10-nona5-point-control owns
its final discharge and the unconditional half-Sylow theorem.
Source: Aschbacher--Smith Theorem C, A.3.12 and 10.2.6, pp.33,47--48,748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

/-- Odd-core removal identifies the central quotient with the literal two-core quotient. -/
theorem ContainingPair.component_coreQuotient_simple
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (K : Subgroup H) (hc : K.IsCComponent) [IsQuasisimple K] :
    IsSimpleGroup (K ⧸ pCore 2 K) := by
  have ho : pPrimeCore 2 K = ⊥ := hc.subnormal.pPrimeCore_eq_bot
    (oddCore_eq_bot_of_moduleChoice hchoice hmany D hn hna C.half_le) K
  have hz : center K = pCore 2 K := IsQuasisimple.center_eq_pCore ho
  let qk : (K ⧸ pCore 2 K) ≃* (K ⧸ center K) :=
    QuotientGroup.quotientMulEquivOfEq hz.symm
  exact
    (MulEquiv.isSimpleGroup_congr qk).mpr IsQuasisimple.simple

/-- The genuine Theorem C catalogue applies to each quasisimple containing component. -/
theorem ContainingPair.component_coreQuotient_theoremC
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (K : Subgroup H) (hc : K.IsCComponent) [IsQuasisimple K] :
    Section02.LocalModels.TheoremCModel (K ⧸ pCore 2 K) := by
  let := C.component_coreQuotient_simple hchoice hmany hn hna K hc
  have hs := D.simpleQTKE.twoLocal_sqtk C.maximal.1
  have hKsq : IsSQTK KnownSimple.IsKnownSimple K := ⟨
    hs.stronglyQuasithin.of_injective K.subtype K.subtype_injective,
    hs.isKGroup.of_injective K.subtype K.subtype_injective⟩
  have hsqtk : IsSQTK KnownSimple.IsKnownSimple (K ⧸ pCore 2 K) := by
    refine ⟨?_,hKsq.isKGroup.quotient _⟩
    intro p hp hop
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p hop _ pCore_isPGroup).trans
      (hKsq.stronglyQuasithin p hp hop)
  exact ChapterA.Section03.SourceComponents.sourceTheoremC_to_local
    (Group.IsPerfect.not_isMulCommutative (K ⧸ pCore 2 K))
    (ChapterA.Section02.theoremC_knownSimple (G := K ⧸ pCore 2 K) inferInstance
      (Group.IsPerfect.not_isMulCommutative (K ⧸ pCore 2 K))
      hsqtk.stronglyQuasithin hsqtk.isKGroup)

/-- All eight rank-two alternatives are excluded with their actual model isomorphisms. -/
theorem ContainingPair.impossible_of_rankTwo_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hm : Section02.LocalModels.RankTwoTheoremC (K₁ ⧸ pCore 2 K₁) ∨
      Section02.LocalModels.RankTwoTheoremC (K₂ ⧸ pCore 2 K₂)) : False := by
  rcases hm with hm | hm
  all_goals cases hm with
  | linear n hnn he =>
      exact C.impossible_of_binary_linear_three_quotient hchoice hmany hn hna hnn (by aesop)
  | symplectic n hnn he =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      let e' := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
      first
      | exact C.impossible_of_first_symplectic_four_quotient hchoice hmany hn hna (by omega) hF e'
      | exact C.impossible_of_second_symplectic_four_quotient hchoice hmany hn hna (by omega) hF e'
  | g2 n hnn he =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
      let := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow
        (by simpa only [Nat.card_eq_fintype_card] using hF)
      have hlarge : 2 < Nat.card F := by
        rw [hF]
        exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
          (Nat.pow_le_pow_right (by decide) hnn)
      first
      | exact C.impossible_of_first_g2_quotient hchoice hmany hn hna hlarge e
      | exact C.impossible_of_second_g2_quotient hchoice hmany hn hna hlarge e
  | triality n hnn he =>
      exact C.impossible_of_triality_model hchoice hmany hn hna (n := n) (by omega) (by aesop)
  | ree m hmm he => exact C.impossible_of_ree_model hn hmm (by aesop)
  | symplectic_derived he =>
      exact C.impossible_of_binary_symplectic_derived_quotient hchoice hmany hn hna (by aesop)
  | g2_derived he =>
      exact C.impossible_of_binary_g2_derived_quotient hchoice hmany hn hna (by aesop)
  | tits he => exact C.impossible_of_tits_quotient hchoice hmany hn hna (by aesop)

/-- A strict first containing component must have one of the actual sporadic quotients. -/
theorem ContainingPair.first_strict_sporadic_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hstrict : L.subgroupOf H < K₁) :
    ∃ name : ClassificationModels.SporadicName, name ≠ .j3 ∧
      Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* name.Carrier) := by
  let := C.first_quasisimple_of_strict hchoice hmany hn hna hstrict
  have hm := C.component_coreQuotient_theoremC hchoice hmany hn hna K₁ C.first_component
  cases hm with
  | alternating n hnn he => exact (C.impossible_of_alternating_quotient hchoice hmany hn hna hnn.1 hnn.2 (.inl he)).elim
  | linear_odd p e hp ho he _ hm =>
      exact (C.impossible_of_odd_linear_two_model hchoice hmany hn hna hp ho he (.inl hm)).elim
  | three_odd p hp ho unitary he =>
      apply (C.impossible_of_first_strict_odd_three_quotient hchoice hmany hn hna hstrict hp ho ?_).elim
      cases unitary
      · exact .inl he
      · exact .inr he
  | rank_one hm =>
      exact (hstrict.ne (C.first_eq_of_solvable_sylow_quotient
        (ChapterA.Section03.SourceEmbeddings.bender_solvable_proper_sylow_overgroup hm))).elim
  | rank_two hm => exact (C.impossible_of_rankTwo_quotient hchoice hmany hn hna (.inl hm)).elim
  | binary_linear n hnn he =>
      exact (C.impossible_of_binary_linear_model hchoice hmany hn hna
        (by rcases hnn with rfl | rfl <;> omega) (by rcases hnn with rfl | rfl <;> omega) (.inl he)).elim
  | sporadic name hne he => exact ⟨name,hne,he⟩
  | janko_one he => exact (C.impossible_of_janko_one_quotient hchoice hmany hn hna (.inl he)).elim

/-- The same reduction preserves the original opposite factor and exchanger. -/
theorem ContainingPair.second_strict_sporadic_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hstrict : (L.map (MulAut.conj t).toMonoidHom).subgroupOf H < K₂) :
    ∃ name : ClassificationModels.SporadicName, name ≠ .j3 ∧
      Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* name.Carrier) := by
  let := C.second_quasisimple_of_strict hchoice hmany hn hna hstrict
  have hm := C.component_coreQuotient_theoremC hchoice hmany hn hna K₂ C.second_component
  cases hm with
  | alternating n hnn he => exact (C.impossible_of_alternating_quotient hchoice hmany hn hna hnn.1 hnn.2 (.inr he)).elim
  | linear_odd p e hp ho he _ hm =>
      exact (C.impossible_of_odd_linear_two_model hchoice hmany hn hna hp ho he (.inr hm)).elim
  | three_odd p hp ho unitary he =>
      apply (C.impossible_of_second_strict_odd_three_quotient hchoice hmany hn hna hstrict hp ho ?_).elim
      cases unitary
      · exact .inl he
      · exact .inr he
  | rank_one hm =>
      exact (hstrict.ne (C.second_eq_of_solvable_sylow_quotient
        (ChapterA.Section03.SourceEmbeddings.bender_solvable_proper_sylow_overgroup hm))).elim
  | rank_two hm => exact (C.impossible_of_rankTwo_quotient hchoice hmany hn hna (.inr hm)).elim
  | binary_linear n hnn he =>
      exact (C.impossible_of_binary_linear_model hchoice hmany hn hna
        (by rcases hnn with rfl | rfl <;> omega) (by rcases hnn with rfl | rfl <;> omega) (.inr he)).elim
  | sporadic name hne he => exact ⟨name,hne,he⟩
  | janko_one he => exact (C.impossible_of_janko_one_quotient hchoice hmany hn hna (.inr he)).elim
end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
