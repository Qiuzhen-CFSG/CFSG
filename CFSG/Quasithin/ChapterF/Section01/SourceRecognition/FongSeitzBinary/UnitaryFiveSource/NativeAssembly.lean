module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.QuotientData
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.Generation

/-!
# Generation and assembly for the synchronized U₅ source

The literal positive subgroup and any pair of marked simple lifts generate
the whole source quotient, by its original unipotent normal generation.
Thus the source equations construct FiveData without a generation premise
or any surjectivity claim about the Cartan parametrization.
Source: Fong--Seitz II (8C), pp.202--210; DGS Theorem D, p.224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource

variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)

include e h in
/-- Full positive coverage and the two actual Weyl classes force generation. -/
theorem marked_fullGenerated {RA RD RC RB H : Type*}
    [Group RA] [Group RD] [Group RC] [Group RB] [Group H]
    (r : PositiveMaps (X ⧸ Q.D) RA RD RC RB) (cartan : H →* (X ⧸ Q.D))
    {j : Fin 2} (lifts : MarkedWeyl.Lifts Q j) (hU : r.generated = split.U) :
    ReflectionLaws.fullGenerated r cartan (lifts.s : X ⧸ Q.D) (lifts.t : X ⧸ Q.D) = ⊤ := by
  let n : Fin 2 → Q.tits.N := fun i => if i = j then lifts.t else lifts.s
  have hn (i : Fin 2) : QuotientGroup.mk'
      ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) (n i) = Q.simple i := by
    dsimp only [n]
    split_ifs with hi
    · simpa only [hi] using lifts.t_class
    · have he : 1-j = i := by fin_cases i <;> fin_cases j <;> simp_all
      simpa only [he] using lifts.s_class
  apply UnitarySource.marked_generate_of_unipotent_and_lifts Q e h split n hn
  · rw [← hU]
    exact (show r.generated ≤ r.borel cartan from le_sup_left).trans
      (fun x hx => Subgroup.subset_closure (Or.inl hx))
  · intro i
    apply Subgroup.subset_closure
    apply Or.inr
    dsimp only [n]
    split_ifs
    · exact Or.inr (Set.mem_singleton _)
    · exact Or.inl rfl

variable {E : Type*} [Field E] [CharP E 2]

/-- The actual root equations and Cartan placement construct the presentation
data; generation is proved using the original F.1.1 source. -/
def nativeFiveData (J : HermitianForm 5 E) {j : Fin 2}
    (r : PositiveMaps (X ⧸ Q.D) (Multiplicative E) (FivePositive.Parameter J)
      (Multiplicative E) (FivePositive.Parameter J))
    (cartan : (Eˣ × Eˣ) →* (X ⧸ Q.D)) (lifts : MarkedWeyl.Lifts Q j)
    (hU : r.generated = split.U) (hH : cartan.range ≤ Q.tits.B ⊓ Q.tits.N)
    (heq : (FivePresentation.parameters J).Satisfies
      (Presentation.Generator.ofMaps r cartan (lifts.s : X ⧸ Q.D) (lifts.t : X ⧸ Q.D))) :
    UnitaryPresentation.FiveData Q split j J where
  roots := r
  cartan := cartan
  lifts := lifts
  equations := heq
  generate := marked_fullGenerated Q split e h r cartan lifts hU
  positive_le := hU.le
  cartan_le := hH

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
