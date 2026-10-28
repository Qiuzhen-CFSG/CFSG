module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.PositiveCoefficients
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialityPresentation.PositiveSubgroup
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderedProducts

/-!
# Coefficient-stage application on the marked source quotient

Match the six original root ranges to the canonical positive roots of the
same finite quotient Q. Carter's existing ordered coordinates then prove
that their closure is exactly split.U; neither generation nor a map from
the triality model is assumed. This works for either alternating orientation.
Compatible scalar transport and the third-short-root Frobenius shift leave
all six original ranges unchanged.

The coefficient calculation supplies the fifteen equations of the existing
triality positive consumer. Its native homomorphism therefore has exactly
the original marked S image. For the generated numerator this is the literal
Q.q image; for a geometric numerator it uses the supplied amalgam marking
into Q.standardAmalgam and requires no descent to the generated group.

This is an application of the intermediate CoefficientStage contract. The
source reconstruction must still produce that contract and the root-range
placements from 6E(b), and must prove the signed/torus/Weyl contracts.
Sources: Fong--Seitz II (9.28)--(9.35); Carter 2.5.10--2.5.17;
DGS, Groups and Graphs, Theorem D, printed p.224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource

private theorem positiveClosure_le_iff {Y : Type*} [Group Y] {n : ℕ} {hn : 0 < n}
    (L : PositiveRoots n hn Y) (T : Subgroup Y) :
    L.positiveClosure ≤ T ↔ (∀ i, (L.shortRoot i).range ≤ T) ∧
      (∀ i, (L.longRoot i).range ≤ T) := by
  rw [PositiveRoots.positiveClosure, Subgroup.closure_le]
  constructor
  · intro h
    constructor
    · intro i x hx
      obtain ⟨x, rfl⟩ := hx
      apply h
      fin_cases i
      · exact ⟨(0, (fun _ => x.toAdd, 0)), rfl⟩
      · exact ⟨(2, (fun _ => x.toAdd, 0)), rfl⟩
      · exact ⟨(3, (fun _ => x.toAdd, 0)), rfl⟩
    · intro i x hx
      obtain ⟨x, rfl⟩ := hx
      apply h
      fin_cases i
      · exact ⟨(1, (0, fun _ => x.toAdd)), rfl⟩
      · exact ⟨(4, (0, fun _ => x.toAdd)), rfl⟩
      · exact ⟨(5, (0, fun _ => x.toAdd)), rfl⟩
  · rintro ⟨hs, hl⟩ x ⟨⟨i,v⟩,rfl⟩
    fin_cases i
    · exact hs 0 ⟨_,rfl⟩
    · exact hl 0 ⟨_,rfl⟩
    · exact hs 1 ⟨_,rfl⟩
    · exact hs 2 ⟨_,rfl⟩
    · exact hl 1 ⟨_,rfl⟩
    · exact hl 2 ⟨_,rfl⟩

variable {F Y : Type*} [Field F] [Group Y] {σ : F ≃+* F}
  {n : ℕ} {hn : 0 < n}
namespace RawRoots
variable (r : RawRoots σ Y) (e : ScalarMarking (binaryParameters n hn) σ)

/-- The original six subgroup ranges, before any field or orbit reparametrization. -/
def ranges (i : Fin 6) : Subgroup Y :=
  ![(r.short 0).range, (r.long 0).range, (r.short 1).range,
    (r.short 2).range, (r.long 1).range, (r.long 2).range] i

@[simp] theorem markedShort_range (i : Fin 3) : (r.markedShort i).range = (r.short i).range := by
  by_cases hi : i = 2
  · ext x
    simp only [markedShort, hi, ↓reduceIte, MonoidHom.mem_range, MonoidHom.comp_apply]
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨_,rfl⟩
    · rintro ⟨a,rfl⟩
      obtain ⟨b,hb⟩ := σ.surjective a.toAdd
      exact ⟨.ofAdd b, congrArg (fun t : F => r.short 2 (.ofAdd t)) hb⟩
  · simp only [markedShort, hi, ↓reduceIte]

private theorem scalar_short_range (i : Fin 3) :
    ((e.positiveRoots r.markedShort r.long).shortRoot i).range = (r.markedShort i).range := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨.ofAdd (e.extension.symm a.toAdd),rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨.ofAdd (e.extension a.toAdd), e.positiveRoots_short r.markedShort r.long i a.toAdd⟩

private theorem scalar_long_range (i : Fin 3) :
    ((e.positiveRoots r.markedShort r.long).longRoot i).range = (r.long i).range := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨.ofAdd (e.fixed.symm a.toAdd),rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨.ofAdd (e.fixed a.toAdd), e.positiveRoots_long r.markedShort r.long i a.toAdd⟩

/-- Both compatible field marking and the Frobenius shift preserve the original
six subgroup ranges, so generation can be checked on the canonical source roots. -/
theorem positiveClosure_le_iff_ranges (T : Subgroup Y) :
    (e.positiveRoots r.markedShort r.long).positiveClosure ≤ T ↔ ∀ i, r.ranges i ≤ T := by
  rw [positiveClosure_le_iff]
  simp only [scalar_short_range, scalar_long_range, markedShort_range]
  constructor
  · rintro ⟨hs,hl⟩ i
    fin_cases i
    · exact hs 0
    · exact hl 0
    · exact hs 1
    · exact hs 2
    · exact hl 1
    · exact hl 2
  · intro h
    exact ⟨fun i => by fin_cases i; exact h 0; exact h 2; exact h 3,
      fun i => by fin_cases i; exact h 1; exact h 4; exact h 5⟩

end RawRoots

section Quotient
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (r : RawRoots σ (X ⧸ Q.D)) (e : ScalarMarking (binaryParameters n hn) σ)
  (orientation : Bool) (hm : rotationOrder Q = 6)
  (placement : ∀ A, A ∈ orderedRoots Q split orientation 6 ↔ ∃ i, r.ranges i = A)

include hm placement in
/-- Covering exactly the six canonical positive root subgroups proves generation
of the same split U, for either source orientation. -/
theorem positiveClosure_eq_unipotent :
    (e.positiveRoots r.markedShort r.long).positiveClosure = split.U := by
  apply le_antisymm
  · apply (r.positiveClosure_le_iff_ranges e split.U).mpr
    intro i
    have hi := orderedRoots_le Q split orientation (rotationOrder Q) le_rfl (r.ranges i)
      (by rw [hm]; exact (placement _).mpr ⟨i,rfl⟩)
    simpa only [alternatingWord_longest, longest_inv, rootIntersection_longest] using hi
  · let C := (e.positiveRoots r.markedShort r.long).positiveClosure
    have hr : ∀ i, r.ranges i ≤ C := (r.positiveClosure_le_iff_ranges e C).mp le_rfl
    have hC (A) (hA : A ∈ orderedRoots Q split orientation (rotationOrder Q)) : A ≤ C := by
      rw [hm] at hA
      obtain ⟨i,rfl⟩ := (placement A).mp hA
      exact hr i
    intro x hx
    let u : split.U := ⟨x,hx⟩
    let coordinates := unipotentOrderedCoordinates Q split orientation
    have hmem := rootProduct_mem _ C hC (coordinates.symm u)
    have he : rootProduct _ (coordinates.symm u) = x :=
      (unipotentOrderedCoordinates_apply Q split orientation (coordinates.symm u)).symm.trans
        (congrArg Subtype.val (coordinates.apply_symm_apply u))
    exact he ▸ hmem

variable [Finite F] [CharP F 2] (d : r.CoefficientStage e)

/-- A coefficient-stage application to the literal source quotient. The
source module construction still has to produce d and the canonical placements. -/
def positiveRootData : TrialityPresentation.PositiveRootData Q split n hn σ where
  scalars := e
  shortRoot := r.markedShort
  longRoot := r.long
  relations := d.relations
  positive := positiveClosure_eq_unipotent Q split r e orientation hm placement

/-- The positive map is onto exactly the original marked S image. The statement
also applies to a geometric marking without descent from its numerator. -/
theorem nativeHom_range_marked {G : Type*} [Group G]
    {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam) (h : HypothesisF11 L S) :
    (positiveRootData Q split r e orientation hm placement d).nativeHom.range =
      (MarkedLocal.sylowMap Q marking h).range :=
  (positiveRootData Q split r e orientation hm placement d).nativeHom_range_marked marking h

end Quotient

/-- For the generated source numerator the image uses the actual quotient map Q.q. -/
theorem nativeHom_range_original [Finite F] [CharP F 2]
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (r : RawRoots σ ((generated L S) ⧸ Q.D)) (e : ScalarMarking (binaryParameters n hn) σ)
    (orientation : Bool) (hm : rotationOrder Q = 6)
    (placement : ∀ A, A ∈ orderedRoots Q split orientation 6 ↔ ∃ i, r.ranges i = A)
    (d : r.CoefficientStage e) :
    (positiveRootData Q split r e orientation hm placement d).nativeHom.range =
      (S.subgroupOf (generated L S)).map Q.q :=
  TrialityPresentation.nativeHom_range_original h Q split
    (positiveRootData Q split r e orientation hm placement d)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource
