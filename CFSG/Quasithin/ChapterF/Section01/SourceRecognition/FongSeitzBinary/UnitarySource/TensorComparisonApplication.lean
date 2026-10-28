module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.TensorEquationApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.OriginalComparisons
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.ModelComparisons
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionCatalogue

/-!
# U₄ recognition from the original quadratic profile

The complete source FourData gives the projective unitary equivalence on
the same quotient. Restriction to both full parabolics and their whole
intersection gives one compatible marked comparison, with literal source
quotient formulas in the original specialization. The catalogue application
transports the constructed field to the published matrix-field convention;
no field identification or presentation relation remains as a premise.
Both endpoint orientations and the fixed-field orders two and four remain.

The original quadratic profile and remainder containments are earlier-source
inputs; this module discharges their U₄ coordinate and comparison branch.
Source: Fong--Seitz I (6A)(b), pp.37--38; II (8B), pp.201--202,
especially (8.7)--(8.9); DGS Theorem D, p.224.
-/

@[expose] public noncomputable section
open Subgroup Representation Matrix Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
open Theory.PSL2.SemilinearCoverage
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open Representation.OrthogonalFourMinus Representation.OrthogonalFourMinus.FiniteModel
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
section Marked
variable {G X F k : Type*} [Group G] [Group X]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (si : RootReflection Q split i) (sj : RootReflection Q split j)
  (fi : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,F))
  (fj : (S ⊔ L j).subgroupOf (parabolic L S j) →* SL(2,k))
  (hfi : Function.Surjective fi) (hfj : Function.Surjective fj)
  (hki : fi.ker = (pCore 2 (parabolic L S i)).subgroupOf ((S ⊔ L i).subgroupOf (parabolic L S i)))
  (hkj : fj.ker = (pCore 2 (parabolic L S j)).subgroupOf ((S ⊔ L j).subgroupOf (parabolic L S j)))
  (hfields : Nat.card F = Nat.card k ^ 2)
  (hindexi : (commonBorel L S).relIndex (parabolic L S i) = Nat.card F + 1)
  (hindexj : (commonBorel L S).relIndex (parabolic L S j) = Nat.card k + 1)
  (helem : IsElementaryAbelian 2 ((parabolic L S i).pCoreIn 2))
  (hQi : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := S) i
    IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
  (hQj : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := S) j
    IsElementaryAbelian 2 (S ⧸ ((parabolic L S j).pCoreIn 2).subgroupOf S))
  (hne : ⁅(parabolic L S j).pCoreIn 2,(parabolic L S j).pCoreIn 2⁆ ≠ ⊥)
  (n : ℕ) [NeZero n] (hk : Nat.card k = 2^n)
open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open UnitaryPresentation

include mark h hVi fi hfi hki hVj fj hfj hkj hfields hindexi hindexj helem hQi hQj hne hk hm hij in
/-- The actual U₄ projective equivalence and full marked comparison on any
source-marked quotient, including a geometric universal quotient. -/
theorem marked_quadratic_unitaryFour_comparison :
    ∃ (e : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n)) ≃* (X ⧸ Q.D))
      (c : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
        (MarkedAmalgam.flag
          ((pointParabolicSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))).map
            (project (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))))
          ((planeParabolicSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))).map
            (project (Field n) (form (Field n) (conjugation n) (conjugation_involutive n)))) j)),
      (∀ a : parabolic L S 0, (c.left a : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))) =
        e.symm (mark.left a : X ⧸ Q.D)) ∧
      (∀ a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G),
        (c.middle a : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))) =
          e.symm (mark.middle a : X ⧸ Q.D)) ∧
      (∀ a : parabolic L S 1, (c.right a : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))) =
        e.symm (mark.right a : X ⧸ Q.D)) := by
  obtain ⟨d,_⟩ := marked_quadratic_fourData Q mark h split hm i j hij hVi hVj fi fj hfi hfj hki hkj
    hfields hindexi hindexj helem hQi hQj hne n hk
  exact ⟨d.projectiveEquiv (conjugation n) (conjugation_involutive n) hm,
    FourOriginal.comparison Q mark split hm (conjugation n) (conjugation_involutive n) d,
    fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

include mark h hVi fi hfi hki hVj fj hfj hkj hfields hindexi hindexj helem hQi hQj hne hk hm hij in
/-- The same constructed source data use the published matrix-field
convention, by the literal equality 2n=n2. Both orientations survive. -/
theorem marked_quadratic_unitaryFour_modelData :
    Nonempty (FourData Q split j (GreenBook.LieModels.UnitaryFour.fieldConj n)
      (GreenBook.LieModels.UnitaryFour.fieldConj_involutive n (NeZero.pos n))) := by
  obtain ⟨d,_⟩ := marked_quadratic_fourData Q mark h split hm i j hij hVi hVj fi fj hfi hfj hki hkj
    hfields hindexi hindexj helem hQi hQj hne n hk
  let T (a : ℕ) : Prop := ∃ hi : Function.Involutive (iterateFrobeniusEquiv (GaloisField 2 a) 2 n),
    Nonempty (FourData Q split j (iterateFrobeniusEquiv (GaloisField 2 a) 2 n) hi)
  have hT : T (2*n) := ⟨conjugation_involutive n,⟨d⟩⟩
  have hT' : T (n*2) := (Nat.mul_comm 2 n) ▸ hT
  obtain ⟨hi,hdata⟩ := hT'
  exact hdata


include mark h hVi fi hfi hki hVj fj hfj hkj hfields hindexi hindexj helem hQi hQj hne hk hm hij in
/-- Literal catalogue entry consumed by Chapter12, with all source equations
and generation discharged from the original quadratic profile. -/
theorem marked_quadratic_unitaryFour_catalogue :
    Chapter6.Source.RankOneGeneric.Global.ConcreteAmalgamComparison
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) := by
  obtain ⟨d⟩ := marked_quadratic_unitaryFour_modelData Q mark h split hm i j hij hVi hVj fi fj hfi hfj hki hkj
    hfields hindexi hindexj helem hQi hQj hne n hk
  apply Chapter6.Source.RankOneGeneric.Global.ConcreteAmalgamComparison.unitary n (NeZero.pos n)
  fin_cases j
  · exact Or.inl ⟨mark.trans (FourModel.forwardComparison n (NeZero.pos n) Q split hm d)⟩
  · exact Or.inr ⟨mark.trans (FourModel.reverseComparison n (NeZero.pos n) Q split hm d)⟩

end Marked

open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag

variable {G F k : Type*} [Group G]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (si : RootReflection Q split i) (sj : RootReflection Q split j)
  (fi : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,F))
  (fj : (S ⊔ L j).subgroupOf (parabolic L S j) →* SL(2,k))
  (hfi : Function.Surjective fi) (hfj : Function.Surjective fj)
  (hki : fi.ker = (pCore 2 (parabolic L S i)).subgroupOf ((S ⊔ L i).subgroupOf (parabolic L S i)))
  (hkj : fj.ker = (pCore 2 (parabolic L S j)).subgroupOf ((S ⊔ L j).subgroupOf (parabolic L S j)))
  (hfields : Nat.card F = Nat.card k ^ 2)
  (hindexi : (commonBorel L S).relIndex (parabolic L S i) = Nat.card F + 1)
  (hindexj : (commonBorel L S).relIndex (parabolic L S j) = Nat.card k + 1)
  (helem : IsElementaryAbelian 2 ((parabolic L S i).pCoreIn 2))
  (hQi : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := S) i
    IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
  (hQj : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := S) j
    IsElementaryAbelian 2 (S ⧸ ((parabolic L S j).pCoreIn 2).subgroupOf S))
  (hne : ⁅(parabolic L S j).pCoreIn 2,(parabolic L S j).pCoreIn 2⁆ ≠ ⊥)
  (n : ℕ) [NeZero n] (hk : Nat.card k = 2^n)

include h hVi fi hfi hki hVj fj hfj hkj hfields hindexi hindexj helem hQi hQj hne hk hm hij in
/-- The full original marked comparison, with Q.q on both endpoints
and their entire overlap. -/
theorem original_quadratic_unitaryFour_comparison :
    ∃ (e : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n)) ≃* ((generated L S) ⧸ Q.D))
      (c : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
        (MarkedAmalgam.flag
          ((pointParabolicSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))).map
            (project (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))))
          ((planeParabolicSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))).map
            (project (Field n) (form (Field n) (conjugation n) (conjugation_involutive n)))) j)),
      (∀ a : parabolic L S 0, (c.left a : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))) =
        e.symm (Q.q ⟨a,parabolic_le_generated 0 a.property⟩)) ∧
      (∀ a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G),
        (c.middle a : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))) =
          e.symm (Q.q ⟨a,parabolic_le_generated 0 a.property.1⟩)) ∧
      (∀ a : parabolic L S 1, (c.right a : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))) =
        e.symm (Q.q ⟨a,parabolic_le_generated 1 a.property⟩)) := by
  obtain ⟨e,c,hl,hm',hr⟩ := marked_quadratic_unitaryFour_comparison Q (originalMarkedIso Q) h split
    hm i j hij hVi hVj fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne n hk
  refine ⟨e,c,?_,?_,?_⟩
  · intro a
    rw [hl,originalMarkedIso_left_apply]
  · intro a
    rw [hm',originalMarkedIso_middle_apply]
  · intro a
    rw [hr,originalMarkedIso_right_apply]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
