module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryFiveSource.RootCharts
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.ActorCartanApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.ActorWeylApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RootCoordinates.SourceProducts

/-!+# Initial U₅ charts on the original source quotient

The original SL₂ epimorphism constructs the linear panel marking. Together
with the given projective unitary panel marking it constructs four faithful
root charts, retaining both full nonabelian Hermitian roots. The same source
Weyl section supplies both lifts. Ordered products prove unique coordinates
on the literal Q.q-image of S and generation of the whole quotient.

This removes chart coverage and generation callbacks at the genuine earlier
profile boundary, including q=2 and q=4. The common field labels are initial
choices, not yet compatible module coordinates. The natural/Hermitian module
realization, remaining mixed equations, labelled Cartan and Weyl equations,
and FiveData/marked-comparison assembly remain to be proved.

Source: Fong--Seitz I (5C), (6A)(c); II (8C), pp.202--210.
Consumers: the positive maps, positive placement and generation fields of
UnitaryPresentation.FiveData, on the same marked/original quotient.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource

variable {G X K E : Type*} [Group G] [Group X]
  [Field K] [Finite K] [CharP K 2] [Field E] [Finite E] [CharP E 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)
  (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
  (hK : Nat.card K = (2^n)^2) (hE : Nat.card E = (2^n)^2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hm : rotationOrder Q = 4) (i : Fin 2)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split (1-i) ≤ localKernel Q (1-i))
  (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
  (hf : Function.Surjective f)
  (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf
    ((S ⊔ L i).subgroupOf (parabolic L S i)))
  (ν : localGroup Q split (1-i) ≃* ProjectiveSpecialUnitaryMatrixGroup J)

/-- The source construction uses the original epimorphism and one actual Weyl section. -/
def sourceRootCharts : PositiveMaps (X ⧸ Q.D) (Multiplicative E)
    (FivePositive.Parameter (fiveForm J)) (Multiplicative E)
    (FivePositive.Parameter (fiveForm J)) :=
  rootCharts Q split J hn hK hE hfixed hJ i hVi hVj
    (UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk) ν
    (UnitarySource.quadrangleLifts Q split hm (1-i)).s
    (UnitarySource.quadrangleLifts Q split hm (1-i)).t

local notation "r" => sourceRootCharts Q split e h J hn hK hE hfixed hJ hm i hVi hVj f hf hk ν
local notation "w" => UnitarySource.quadrangleLifts Q split hm (1-i)

private theorem s_class :
    QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) (w).s = Q.simple i := by
  have he : 1-(1-i) = i := by fin_cases i <;> rfl
  simpa only [he] using (w).s_class

omit [CharP E 2]

/-- The original earlier inputs supply faithful, exhaustive four-root coordinates. -/
theorem sourceRootCharts_coordinates : Function.Injective (chartWord Q r) ∧
    Set.range (chartWord Q r) = (split.U : Set (X ⧸ Q.D)) ∧ (r).generated = split.U :=
  rootCharts_coordinates Q split J hn hK hE hfixed hJ i hVi hVj
    (UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk) ν (w).s (w).t
    (s_class Q split hm i) (w).t_class hm

/-- All four chart ranges are the actual simple and crossed roots. -/
theorem sourceRootCharts_ranges :
    (r).A.range = simpleRoot Q split i ∧ (r).B.range = simpleRoot Q split (1-i) ∧
    (r).D.range = rootAt Q split (1-i) (Q.simple i) ∧
    (r).C.range = rootAt Q split i (Q.simple (1-i)) := by
  obtain ⟨ha,hb⟩ := rootCharts_simple_ranges Q split J hn hK hE hfixed hJ i hVi hVj
    (UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk) ν (w).s (w).t
  obtain ⟨hd,hc⟩ := rootCharts_cross_ranges Q split J hn hK hE hfixed hJ i hVi hVj
    (UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk) ν (w).s (w).t
    (s_class Q split hm i) (w).t_class
  exact ⟨ha,hb,hd,hc⟩

/-- Three actual positive relations, with the full Hermitian B and D parameters. -/
theorem sourceRootCharts_commuting :
    (∀ a d, Commute ((r).A a) ((r).D d)) ∧
    (∀ c d, Commute ((r).C c) ((r).D d)) ∧
    (∀ b c, Commute ((r).B b) ((r).C c)) :=
  rootCharts_commuting Q split J hn hK hE hfixed hJ i hVi hVj
    (UnitarySource.markedLinearLocalMarking Q e h split i hVi f hf hk) ν (w).s (w).t
    (s_class Q split hm i) (w).t_class hm

/-- These concrete root charts and lifts generate the entire marked quotient.
The later Cartan choice does not add a generation premise. -/
theorem sourceRootCharts_generate (cartan : (Eˣ × Eˣ) →* X ⧸ Q.D) :
    ReflectionLaws.fullGenerated r cartan ((w).s : X ⧸ Q.D) ((w).t : X ⧸ Q.D) = ⊤ :=
  UnitarySource.marked_positive_fullGenerated Q split hm e h (1-i) r cartan
    (sourceRootCharts_coordinates Q split e h J hn hK hE hfixed hJ hm i hVi hVj f hf hk ν).2.2

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
variable {G K E : Type*} [Group G]
  [Field K] [Finite K] [CharP K 2] [Field E] [Finite E] [CharP E 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) (h : HypothesisF11 L S)
  (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
  (hK : Nat.card K = (2^n)^2) (hE : Nat.card E = (2^n)^2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hm : rotationOrder Q = 4) (i : Fin 2)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split (1-i) ≤ localKernel Q (1-i))
  (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
  (hf : Function.Surjective f)
  (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf
    ((S ⊔ L i).subgroupOf (parabolic L S i)))
  (ν : localGroup Q split (1-i) ≃* ProjectiveSpecialUnitaryMatrixGroup J)

local notation "r" => sourceRootCharts Q split (originalMarkedIso Q) h J hn hK hE hfixed hJ
  hm i hVi hVj f hf hk ν

omit [CharP E 2]

/-- The literal original Sylow image has unique full A,D,C,B coordinates. -/
theorem originalS_unique_coordinates (x : (generated L S) ⧸ Q.D)
    (hx : x ∈ (S.subgroupOf (generated L S)).map Q.q) :
    ∃! p : Multiplicative E × FivePositive.Parameter (fiveForm J) ×
      Multiplicative E × FivePositive.Parameter (fiveForm J), chartWord Q r p = x := by
  obtain ⟨hi,hr,_⟩ := sourceRootCharts_coordinates Q split (originalMarkedIso Q) h J
    hn hK hE hfixed hJ hm i hVi hVj f hf hk ν
  rw [quotient_sourceS_image_eq_unipotent h Q split] at hx
  change x ∈ (split.U : Set ((generated L S) ⧸ Q.D)) at hx
  rw [←hr] at hx
  obtain ⟨p,hp⟩ := hx
  exact ⟨p,hp,fun q hq => hi (hq.trans hp.symm)⟩

/-- Every full chart word has a literal original-S representative under Q.q. -/
theorem originalS_coordinate_representative
    (p : Multiplicative E × FivePositive.Parameter (fiveForm J) ×
      Multiplicative E × FivePositive.Parameter (fiveForm J)) :
    ∃ a : S.subgroupOf (generated L S), Q.q a.val = chartWord Q r p := by
  have hr := (sourceRootCharts_coordinates Q split (originalMarkedIso Q) h J
    hn hK hE hfixed hJ hm i hVi hVj f hf hk ν).2.1
  have hx : chartWord Q r p ∈ (S.subgroupOf (generated L S)).map Q.q := by
    rw [quotient_sourceS_image_eq_unipotent h Q split]
    change chartWord Q r p ∈ (split.U : Set ((generated L S) ⧸ Q.D))
    rw [←hr]
    exact ⟨p,rfl⟩
  obtain ⟨a,ha,he⟩ := hx
  exact ⟨⟨a,ha⟩,he⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
