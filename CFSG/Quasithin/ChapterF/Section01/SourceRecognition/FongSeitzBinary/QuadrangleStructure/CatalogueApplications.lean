module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.SuzukiExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryFactorRegularityApplications

/-!
# The original quadrangle catalogue and both core identifications

On a quadrangle with one original linear factor, the opposite quotient
is linear, projective unitary or special unitary. The complete catalogue
excludes every Suzuki and D10 case, including the small solvable models.
Independently the affine-cover argument proves regularity at both
endpoints and identifies the preimages with the original two-cores.

These conclusions are applied to the literal source quotient and the
Chapter 12 prepared pair with its proper-K/full KnownSimple hypotheses.
The selected linear comparison and the all-fields mixed unitary profile
consume precisely these actual factor and core data. Original quotient
construction, Weyl selection and the independent U5 equations retain
their producers; no full seven-row comparison is claimed here.

Source: Fong--Seitz I (5I),(6A), pp.31--37; DGS (11.6)--(11.8),
pp.173--176 and Theorem D, p.224; AS F.1.1--3 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G F : Type*} [Group G] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The actual quotient retains both original cores and every remaining
opposite linear or unitary factor, without a regularity premise. -/
theorem original_quadrangle_factor_catalogue
    (Q : SourceQuotient L S) (split : SplitData Q.tits) (h : HypothesisF11 L S)
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F)) :
    (∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
      (simpleRemainder Q split k).comap (MarkedLocal.endpointMap Q (originalMarkedIso Q) k) =
        pCore 2 (parabolic L S k)) ∧
    ∃ n : ℕ, 0 < n ∧
      (ClassicalGroup.IsPSL ((L j) ⧸ pCore 2 (L j)) 2 (2^n) ∨
       ClassicalGroup.IsPSU ((L j) ⧸ pCore 2 (L j)) 3 (2^n) ∨
       IsSU ((L j) ⧸ pCore 2 (L j)) 3 (2^n)) := by
  exact ⟨MarkedLocal.marked_quadrangle_regularity Q (originalMarkedIso Q) h split hm,
    original_quadrangle_opposite_linear_or_unitary Q (originalMarkedIso Q) h split hm i j hij μi⟩
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The original Chapter 12 linear endpoint selects the opposite catalogue
and both exact core preimages on its marked split quadrangle. -/
theorem rankOne_global_quadrangle_factor_catalogue
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 4) :
    (∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
      (simpleRemainder Q split k).comap (MarkedLocal.endpointMap Q mark k) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) k)) ∧
    ∃ m : ℕ, 0 < m ∧
      (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^m) ∨
       ClassicalGroup.IsPSU (R ⧸ pCore 2 R) 3 (2^m) ∨
       IsSU (R ⧸ pCore 2 R) 3 (2^m)) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hpsl
  let := Fintype.ofFinite F
  let : NeZero n := ⟨by omega⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact ⟨MarkedLocal.marked_quadrangle_regularity Q mark hf split hm,
    QuadrangleStructure.original_quadrangle_opposite_linear_or_unitary Q mark hf split hm
      0 1 (by decide) μ⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
