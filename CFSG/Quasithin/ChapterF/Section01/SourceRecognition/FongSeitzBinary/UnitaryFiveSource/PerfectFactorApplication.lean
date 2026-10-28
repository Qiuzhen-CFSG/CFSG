module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.Chapter12
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.SourceComparisons
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryFactorOrderApplications

/-!
# The actual perfect selected factor closes the U₅ branch

The earlier original-S mixed-factor producer supplies its full profile and
both original endpoint-core preimages. Native recognition applies directly
to that same original marking in orientation one. The quasithin parabolic
embedding forces field four only at the final catalogue application.
Neither a reduced-S profile nor an equation package is an input.
Source: Aschbacher–Smith 12.2.2 and F.1.12; Fong–Seitz II (8C).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

omit D in
private theorem original_five_catalogue {q : ℕ} (hq : IsPrimePow q) (heven : Even q)
    (hG : IsQuasithin G) (M : ChapterF.GreenBook.UnitaryFive.Model q)
    (c : RankTwoAmalgam.Iso (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H))
      (MarkedAmalgam.flag M.leftParabolic M.rightParabolic 1)) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  have hq4 := M.field_size_eq_four_of_parabolic_embedding hq heven hG
    ((parabolic ![L,R] (Global.sourceS L H) 1).subtype.comp c.right.symm.toMonoidHom)
    (Subtype.val_injective.comp c.right.symm.injective)
  subst q
  exact .unitaryFive M (Or.inr ⟨c⟩)

/-- Apply the actual perfect-factor producer to the original marking, retaining
the source degree relation, form, original actor square and both core preimages. -/
theorem rankOne_unitary_five_factor_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (hp : Group.IsPerfect R)
    (Q : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 4)
    {K E : Type*} [Field K] [Finite K] [CharP K 2]
    [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {m : ℕ} (hmpos : 0 < m)
    (hE : Nat.card E = (2^m)^2) (hconj : ∀ x, J.conj x = x^(2^m))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (μ : (L ⧸ pCore 2 L) ≃* PSL(2,K))
    (hfactor : Nonempty ((R ⧸ pCore 2 R) ≃* J.specialSubgroup) ∨
      Nonempty ((R ⧸ pCore 2 R) ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    n = 2*m ∧
    ∃ profile : UnitarySource.Combined.FiveProfile ![L,R] (Global.sourceS L H)
      Q split K E m 0 1,
    profile.form = J ∧
    (∀ a : L, profile.linear_actor (MarkedLocal.originalFactorIntoActor 0 a) =
      Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm (μ (QuotientGroup.mk' _ a))) ∧
    (∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
      (simpleRemainder Q split k).comap (MarkedLocal.endpointMap Q mark k) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) k)) ∧
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  obtain ⟨hdegree,p,hform,hlinear,hcores⟩ :=
    D.rankOne_global_unitary_factor_profile_of_perfect h hmany hn hpsl d hTH hp Q mark split hm
      J hmpos hE hconj hJ μ hfactor
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  have hf := d.hypothesisF11 hi hTH
  obtain ⟨M,f,c,hB,hleft,hmiddle,hright⟩ :=
    profile_model_comparison Q split mark hf hm m hmpos 0 1 (by decide) p
  exact ⟨hdegree,p,hform,hlinear,hcores,original_five_catalogue
    (Nat.prime_two.isPrimePow.pow (Nat.ne_of_gt hmpos))
    (even_two.pow_of_ne_zero (Nat.ne_of_gt hmpos)) hi.qtke.quasithin M c⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
