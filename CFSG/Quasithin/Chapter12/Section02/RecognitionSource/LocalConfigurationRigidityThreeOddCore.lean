module
public import Theory.GroupAction.OddNormalizerElementaryFour
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityThreeCubic

/-!
# Closing dimension-three rigidity and parabolic splitting

The canonical action of N_G(R)/R on the elementary radical R is faithful,
with |R|=16 or 32. Its original Sylow image is an elementary four-group.
The small binary odd-normalizer theorem therefore makes the literal odd
core elementary abelian of exponent three. This discharges the remaining
premise in the residual-normality and central-factor elimination argument.

The source applications now prove N_G(L)=L, O₂(L)=V, the complement to V
inside the literal N_L(U), and the ensuing Gaschütz splitting, with no
additional odd-core, cubic-order, or parabolic-complement input. They retain
the original T and the earlier-source natural and cyclic analyses.

This completes the dimension-three branch of the rigidity step. The
explicit symmetric-group product identification and the higher-dimensional
branch remain with qt-d-12213-local-rigidity.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
original 12.2.25--26, printed pp.805--806.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V U P H : Subgroup G}

/-- The literal quotient's odd core is elementary abelian of exponent three.
The four-group actor is the image of the original Sylow subgroup. -/
theorem oddCore_elementary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V 3)
    (C : CyclicLocalAnalysis T L V 3 H P U)
    (B : LocalRigidityCentralizers T L V U P) :
    IsElementaryAbelian 3 (pPrimeCore 2 (NormalizerQuotient T U)) := by
  let R := radical T U
  let : IsElementaryAbelian 2 R := B.elementary
  let : IsElementaryAbelian 2 (quotientSylow C) := quotientSylow_elementary D A C B
  have he := radical_selfCentralizing h C B
  exact Theory.GroupAction.odd_elementary_of_card_sixteen_or_thirtytwo
    (HigherRigidity.action R he.symm.le) (HigherRigidity.action_injective R he)
    (radical_card C B) (quotientSylow C) (pPrimeCore 2 (NormalizerQuotient T U))
    (quotientSylow_card D A C B) (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
    ((pPrimeCore 2 (NormalizerQuotient T U)).normalizer_eq_top ▸ le_top)

/-- The original source hypotheses discharge the odd-core calculation. -/
theorem source_oddCore_elementary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) :
    IsElementaryAbelian 3 (pPrimeCore 2 (NormalizerQuotient T U)) :=
  oddCore_elementary h D A C (RigidityKernel.source_centralizers h D structural A C hnone)

/-- The complete dimension-three rigidity and literal parabolic splitting
conclusion, with both former odd-core and cubic-order premises discharged. -/
theorem source_parabolic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧ ParabolicSplitting T L V U := by
  let := source_oddCore_elementary h D structural A C hnone
  exact source_parabolic_of_abelian_oddCore h D structural A C hnone hTI inferInstance

/-- The dimension-three branch feeds the exact rigidity-step conclusion.
The higher-dimensional source branch remains with qt-d-12213-local-rigidity. -/
theorem source_rigidity_step_of_dimension_three {d : ℕ}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) (hd : d = 3) :
    (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧
      L.pCoreIn 2 = V ∧ ParabolicSplitting T L V U := by
  subst d
  exact ⟨Or.inl rfl,source_parabolic h D structural A C hnone hTI⟩

/-- The actual Gaschütz consumer, without extra local premises. -/
theorem source_split
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V) :
    SplitLinearConfiguration L V 3 := by
  let := source_oddCore_elementary h D structural A C hnone
  exact source_split_of_abelian_oddCore h D structural A C hnone hTI inferInstance

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRigidity
