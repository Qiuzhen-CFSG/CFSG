module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.ProfileComparisons
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryFactorRegularity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.SuzukiExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearQuadrangleRecognition
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.Exclusion
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFormTransport

/-!
# Quadrangle recognition from the original linear factor

The original opposite-factor catalogue leaves linear, SU₃ and PSU₃ quotients.
The linear branch uses the proved linear quadrangle comparison. In the unitary
branches a Hermitian basis change and the all-fields regularity theorem supply
the complete FiveProfile; the proved U₅ source equations then give the marked
model comparison. Its original parabolic embedding in the quasithin group
forces field four at the final catalogue step.

The mixed-factor comparison retains the prescribed original linear action,
both two-core preimages, the full Borel and all three endpoint/overlap squares.
No perfectness, regularity or presentation equation is an extra premise.
The rotation-four and original linear-factor selections remain explicit.

Source: Aschbacher--Smith F.1.1--3 and F.1.12; DGS (11.8) and Theorem D,
pp.175--176,224; Fong--Seitz I (6A)(c), II (8C).
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleRecognition
open Chapter6.Source.RankOneGeneric
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include mark h split in
/-- The original mixed factors construct the full U₅ comparison for any
Hermitian form and either endpoint orientation. The prescribed linear actor,
both original core preimages and all three marking squares are retained. -/
theorem marked_unitary_factor_model_all_fields
    {K E : Type*} [Field K] [Finite K] [CharP K 2]
    [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,K))
    (hfactor : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ p : UnitarySource.Combined.FiveProfile L S Q split K E n i j,
      p.form = standardForm J ∧
      (∀ a : L i, p.linear_actor (MarkedLocal.originalFactorIntoActor i a) =
        Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm (μi (QuotientGroup.mk' _ a))) ∧
      (∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
        (simpleRemainder Q split k).comap (MarkedLocal.endpointMap Q mark k) =
          pCore 2 (parabolic L S k)) ∧
      ∃ (M : GreenBook.UnitaryFive.Model (2^n)) (f : M.Carrier ≃* (X ⧸ Q.D))
        (c : RankTwoAmalgam.Iso
          (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
            (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
          (MarkedAmalgam.flag M.leftParabolic M.rightParabolic j)),
        M.overlap.map f.toMonoidHom = Q.tits.B ∧
        (∀ a : parabolic L S 0, (c.left a : M.Carrier) = f.symm (mark.left a : X ⧸ Q.D)) ∧
        (∀ a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G),
          (c.middle a : M.Carrier) = f.symm (mark.middle a : X ⧸ Q.D)) ∧
        (∀ a : parabolic L S 1, (c.right a : M.Carrier) = f.symm (mark.right a : X ⧸ Q.D)) := by
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hE hconj
  obtain ⟨C,hC⟩ := exists_standard_basis J (2^n) hE hfixed
  have hfactor' : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* (standardForm J).specialSubgroup) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup (standardForm J)) := by
    rcases hfactor with hs | hp
    · obtain ⟨μ⟩ := hs
      exact Or.inl ⟨μ.trans (specialEquiv J C hC)⟩
    · obtain ⟨μ⟩ := hp
      exact Or.inr ⟨μ.trans (projectiveEquiv J C hC)⟩
  obtain ⟨p,hform,hlinear,hcores⟩ :=
    QuadrangleStructure.marked_unitary_factor_profile_all_fields Q mark h split (standardForm J)
      hn hE hconj rfl hm i j hij μi hfactor'
  exact ⟨p,hform,hlinear,hcores,
    UnitaryFiveSource.profile_model_comparison Q split mark h hm n hn i j hij p⟩

private theorem unitary_five_catalogue [Finite G] {q : ℕ}
    (hq : IsPrimePow q) (heven : Even q) (hqt : IsQuasithin G)
    (M : GreenBook.UnitaryFive.Model q)
    (c : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      (MarkedAmalgam.flag M.leftParabolic M.rightParabolic 1)) :
    Global.ConcreteAmalgamComparison
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) := by
  have hq4 := M.field_size_eq_four_of_parabolic_embedding hq heven hqt
    ((parabolic L S 1).subtype.comp c.right.symm.toMonoidHom)
    (Subtype.val_injective.comp c.right.symm.injective)
  subst q
  exact .unitaryFive M (Or.inr ⟨c⟩)

include mark h split in
/-- A marked quasithin quadrangle with the actual left linear quotient has
a concrete catalogue comparison. The opposite family and all unitary source
relations are constructed; the original parabolic embedding forces field four. -/
theorem marked_quadrangle_catalogue_of_linear_left [Finite G]
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hqt : IsQuasithin G) (hm : rotationOrder Q = 4)
    (μ : ((L 0) ⧸ pCore 2 (L 0)) ≃* PSL(2,K)) :
    Global.ConcreteAmalgamComparison
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) := by
  obtain ⟨n,hn,hfactor⟩ := QuadrangleStructure.original_quadrangle_opposite_linear_or_unitary
    Q mark h split hm 0 1 (by decide) μ
  rcases hfactor with hlinear | hproj | hspecial
  · obtain ⟨F,hF,hfin,hcard,⟨ν⟩⟩ := hlinear
    let := Fintype.ofFinite F
    let : NeZero n := ⟨hn.ne'⟩
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact LinearQuadrangle.marked_linear_quadrangle_catalogue Q mark h split hm μ ν
  all_goals
    obtain ⟨E,hEfield,hfin,J,hcard,hconj,⟨ν⟩⟩ := by assumption
    let := Fintype.ofFinite E
    let : NeZero (n*2) := ⟨Nat.mul_ne_zero hn.ne' (by decide)⟩
    let : CharP E 2 := charP_of_card_eq_prime_pow
      (R := E) (p := 2) (f := n*2) (by simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)
    have hmodel : Nonempty (((L 1) ⧸ pCore 2 (L 1)) ≃* J.specialSubgroup) ∨
        Nonempty (((L 1) ⧸ pCore 2 (L 1)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
      first | exact Or.inl ⟨ν⟩ | exact Or.inr ⟨ν⟩
    obtain ⟨p,_,_,_,M,f,c,_⟩ := marked_unitary_factor_model_all_fields
      Q mark h split J hn hcard hconj hm 0 1 (by decide) μ hmodel
    exact unitary_five_catalogue (Nat.prime_two.isPrimePow.pow hn.ne')
      (even_two.pow_of_ne_zero hn.ne') hqt M c

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleRecognition
