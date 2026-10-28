module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.ModuleApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.MiddleRoots

/-!
# Positive generation from the two canonical simple-root markings

The two actual source Weyl lifts transport the simple root ranges to the
four other canonical hexagon roots. The five-root radical product then
places and generates every positive factor in the same split U. This
removes the independent six-root placement premise from the triality
coefficient consumer. Both source orientations use the given permutation
of the two endpoints; no cardinality argument or perfectness is needed.

Source: Fong--Seitz I (3G) and (6E)(b), with the canonical product proved
in HexagonStructure.MiddleRoots; Carter 2.5.10--17. The rootAt convention
is right conjugation. The selected rank-one Weyl elements are involutions,
so their left conjugation gives precisely these same subgroup transports.
The compatible rank-one maps and the two simple-root identifications remain
source construction obligations.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.RootGeometry
open PinnedApplication
variable {F : Type*} [Field F] [CharP F 2] {σ : F ≃+* F}
  {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (p : RankOnePair σ (X ⧸ Q.D)) (w : WeylPlacement Q p)
  (shortBase : (p.shortOrbit 0).range = simpleRoot Q split (w.indices 0))
  (longBase : (p.longOrbit 0).range = simpleRoot Q split (w.indices 1))

include shortBase in
theorem short_one_rootAt :
    (p.shortOrbit 1).range = rootAt Q split (w.indices 0) (Q.simple (w.indices 1)) := by
  have hr : (p.shortOrbit 1).range = rightConjugate (p.shortOrbit 0).range p.dihedral.b := by
    ext x
    change (∃ t, p.dihedral.B (p.shortOrbit 0 t) = x) ↔ ∃ t, p.shortOrbit 0 t = p.dihedral.B x
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨t,(p.dihedral.B_B _).symm⟩
    · rintro ⟨t,ht⟩
      exact ⟨t, by rw [ht, p.dihedral.B_B]⟩
  rw [hr, shortBase, ← w.long]
  exact (rootAt_eq Q split (w.indices 0) _ (w.lift 1) (w.simple 1)).symm

include shortBase in
theorem short_two_rootAt :
    (p.shortOrbit 2).range =
      rootAt Q split (w.indices 0) (Q.simple (w.indices 1)*Q.simple (w.indices 0)) := by
  have hr : (p.shortOrbit 2).range = rightConjugate (p.shortOrbit 1).range p.dihedral.a := by
    ext x
    change (∃ t, p.dihedral.A (p.shortOrbit 1 t) = x) ↔ ∃ t, p.shortOrbit 1 t = p.dihedral.A x
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨t,(p.dihedral.A_A _).symm⟩
    · rintro ⟨t,ht⟩
      exact ⟨t, by rw [ht, p.dihedral.A_A]⟩
  rw [hr, short_one_rootAt Q split p w shortBase, ← w.short]
  exact rootAt_right Q split (w.indices 0) _ _ (w.lift 0) (w.simple 0)

include shortBase longBase in
theorem ranges_le_unipotent (hm : rotationOrder Q = 6) (i : Fin 6) :
    (rawRoots p).ranges i ≤ split.U := by
  have h01 : w.indices 0 ≠ w.indices 1 := w.indices.injective.ne (by decide)
  have hs := exchanged_roots_le_remainder Q split hm (w.indices 0) (w.indices 1) h01
  have hl := exchanged_roots_le_remainder Q split hm (w.indices 1) (w.indices 0) h01.symm
  fin_cases i
  · change (p.shortOrbit 0).range ≤ split.U
    rw [shortBase]
    exact simpleRoot_le Q split _
  · change (p.longOrbit 0).range ≤ split.U
    rw [longBase]
    exact simpleRoot_le Q split _
  · change (p.shortOrbit 1).range ≤ split.U
    rw [short_one_rootAt Q split p w shortBase]
    exact hs.1.trans inf_le_left
  · change (p.shortOrbit 2).range ≤ split.U
    rw [short_two_rootAt Q split p w shortBase]
    exact hs.2.trans inf_le_left
  · change (p.longOrbit 1).range ≤ split.U
    rw [ModuleApplication.long_one_rootAt Q split p w longBase]
    exact hl.1.trans inf_le_left
  · change (p.longOrbit 2).range ≤ split.U
    rw [ModuleApplication.long_two_rootAt Q split p w longBase]
    exact hl.2.trans inf_le_left

include shortBase longBase in
/-- The canonical five-root radical product proves positive generation from
just the two simple-root identifications, in either orientation. -/
theorem positiveClosure_eq_unipotent {n : ℕ} {hn : 0 < n}
    (e : ScalarMarking (binaryParameters n hn) σ) (hm : rotationOrder Q = 6) :
    (p.signedRoots e).positive.positiveClosure = split.U := by
  change (e.positiveRoots (rawRoots p).markedShort p.longOrbit).positiveClosure = split.U
  let C := (e.positiveRoots (rawRoots p).markedShort p.longOrbit).positiveClosure
  have hr : ∀ i, (rawRoots p).ranges i ≤ C :=
    ((rawRoots p).positiveClosure_le_iff_ranges e C).mp le_rfl
  have ha : (p.shortOrbit 0).range ≤ C := hr 0
  have hb : (p.longOrbit 0).range ≤ C := hr 1
  have hc : (p.shortOrbit 1).range ≤ C := hr 2
  have hd : (p.shortOrbit 2).range ≤ C := hr 3
  have he : (p.longOrbit 1).range ≤ C := hr 4
  have hf : (p.longOrbit 2).range ≤ C := hr 5
  rw [shortBase] at ha
  rw [longBase] at hb
  rw [short_one_rootAt Q split p w shortBase] at hc
  rw [short_two_rootAt Q split p w shortBase] at hd
  rw [ModuleApplication.long_one_rootAt Q split p w longBase] at he
  rw [ModuleApplication.long_two_rootAt Q split p w longBase] at hf
  apply le_antisymm
  · exact ((rawRoots p).positiveClosure_le_iff_ranges e split.U).mpr
      (ranges_le_unipotent Q split p w shortBase longBase hm)
  · have hV : simpleRemainder Q split (w.indices 1) ≤ C := by
      intro x hx
      have hx' : x ∈ (simpleRemainder Q split (w.indices 1) : Set (X ⧸ Q.D)) := hx
      rw [radical_five_product Q split hm (w.indices 0) (w.indices 1)
        (w.indices.injective.ne (by decide))] at hx'
      obtain ⟨abcd,⟨abc,⟨ab,⟨a,ha',b,hb',rfl⟩,c,hc',rfl⟩,d,hd',rfl⟩,e,he',rfl⟩ := hx'
      exact C.mul_mem (C.mul_mem (C.mul_mem (C.mul_mem (ha ha') (he hb'))
        (hd hc')) (hf hd')) (hc he')
    intro x hx
    have hx' : x ∈ (simpleRoot Q split (w.indices 1) : Set (X ⧸ Q.D)) *
        (simpleRemainder Q split (w.indices 1) : Set (X ⧸ Q.D)) :=
      (simpleRoot_mul_remainder Q split _).symm ▸ hx
    obtain ⟨b,hb',v,hv,rfl⟩ := hx'
    exact C.mul_mem (hb hb') (hV hv)
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.RootGeometry
